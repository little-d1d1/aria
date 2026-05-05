import os
import platform
import shutil
import stat
import subprocess
import sys
import tarfile
from pathlib import Path
from typing import List, Optional, Tuple
from urllib.parse import urlparse

GITHUB_REPO = "meelgroup/ttc"

try:
    from importlib.metadata import version as _pkg_version
    VERSION = _pkg_version("ttc")
except Exception:
    # Running from a source checkout with no installed metadata (e.g. dev mode
    # or a bare tarball). The sibling-bin fast path handles these cases, so
    # VERSION only matters on the download branch — which such users won't hit.
    VERSION = "0.0.0"

BOOTSTRAP_WHEEL_PACKAGES = ["pycddlib", "polytope", "z3-solver", "cvxopt"]
# pip-install name → import name. pycddlib installs as `cdd`, z3-solver as `z3`.
BOOTSTRAP_IMPORT_NAMES = ["cdd", "polytope", "z3", "cvxopt"]

NATIVE_BINARIES = ["cvc5", "hall_tool", "lrs", "sample", "volume"]


def _platform_artifact() -> str:
    system = platform.system()
    machine = platform.machine()
    if system == "Linux" and machine == "x86_64":
        return "linux-x86_64"
    if system == "Darwin" and machine == "arm64":
        return "macos-arm64"
    raise RuntimeError(
        f"Unsupported platform: {system}/{machine}. "
        f"Pre-built binaries are available for linux-x86_64 and macos-arm64."
    )


def _state_dir() -> Path:
    d = Path.home() / ".local" / "share" / "ttc" / VERSION
    d.mkdir(parents=True, exist_ok=True)
    return d


def _sibling_bin_dir() -> Optional[Path]:
    """Tarball/install.sh flow ships binaries in <repo>/bin next to ttc.py."""
    candidate = Path(__file__).resolve().parent / "bin"
    if all((candidate / b).exists() for b in NATIVE_BINARIES):
        return candidate
    return None


def _bootstrap_packages_installed() -> bool:
    import importlib.util
    for name in BOOTSTRAP_IMPORT_NAMES:
        if importlib.util.find_spec(name) is None:
            return False
    return True


def _version_candidates(version: str) -> List[str]:
    """Generate plausible Git tag/version spellings for release assets.

    Python package metadata normalizes versions like 1.0.011 to 1.0.11, but a
    GitHub release may still be tagged and archived under the zero-padded form.
    Try the canonical version first, then a small set of padded patch variants.
    """
    candidates = [version]
    parts = version.split(".")
    if len(parts) < 3 or any(not part.isdigit() for part in parts):
        return candidates

    patch = parts[-1]
    if int(patch) == 0:
        return candidates

    for width in (2, 3):
        padded_patch = patch.zfill(width)
        if padded_patch != patch:
            candidate = ".".join(parts[:-1] + [padded_patch])
            if candidate not in candidates:
                candidates.append(candidate)
    return candidates


def _release_candidates(version: str, artifact: str) -> List[Tuple[str, str]]:
    return [
        (
            candidate_version,
            f"https://github.com/{GITHUB_REPO}/releases/download/"
            f"v{candidate_version}/ttc-{candidate_version}-{artifact}.tar.gz",
        )
        for candidate_version in _version_candidates(version)
    ]


def ensure_ready() -> Path:
    sibling = _sibling_bin_dir()
    if sibling is not None and _bootstrap_packages_installed():
        return sibling

    bin_dir = _state_dir() / "bin"
    if all((bin_dir / b).exists() for b in NATIVE_BINARIES) and _bootstrap_packages_installed():
        return bin_dir

    artifact = _platform_artifact()
    import requests

    state = _state_dir()
    override_url = os.environ.get("TTC_ARCHIVE_URL")
    if override_url:
        archive_name = Path(urlparse(override_url).path).name or f"ttc-{VERSION}-{artifact}.tar.gz"
        candidates = [(VERSION, override_url)]
    else:
        archive_name = ""
        candidates = _release_candidates(VERSION, artifact)

    archive_path: Optional[Path] = None
    tried_urls = []
    for candidate_version, url in candidates:
        if override_url:
            candidate_archive_name = archive_name
        else:
            candidate_archive_name = f"ttc-{candidate_version}-{artifact}.tar.gz"

        print(
            f"[ttc] First-run setup: downloading {candidate_archive_name} ...",
            file=sys.stderr,
        )
        archive_path = state / candidate_archive_name

        try:
            with requests.get(url, stream=True) as r:
                r.raise_for_status()
                with open(archive_path, "wb") as f:
                    for chunk in r.iter_content(chunk_size=65536):
                        f.write(chunk)
            break
        except requests.HTTPError as exc:
            if archive_path.exists():
                archive_path.unlink()
            if override_url or exc.response is None or exc.response.status_code != 404:
                raise
            tried_urls.append(url)
            archive_path = None
    else:
        tried = "\n".join(f"  - {url}" for url in tried_urls)
        raise RuntimeError(
            f"Unable to find a release archive for TTC {VERSION} on GitHub.\n"
            f"Tried:\n{tried}"
        )

    assert archive_path is not None

    extract_dir = state / "extract"
    if extract_dir.exists():
        shutil.rmtree(extract_dir)
    extract_dir.mkdir()
    with tarfile.open(archive_path) as tar:
        tar.extractall(extract_dir)
    archive_path.unlink()

    # Glob rather than reconstructing from VERSION — decouples extraction from
    # whatever the archive was named, so a version mismatch between the
    # installed package and the downloaded archive doesn't wedge us.
    stage_candidates = list(extract_dir.glob(f"ttc-*-{artifact}"))
    if len(stage_candidates) != 1:
        raise RuntimeError(
            f"expected exactly one stage dir in {extract_dir}, got {stage_candidates}"
        )
    stage = stage_candidates[0]

    bin_dir.mkdir(exist_ok=True)
    for b in NATIVE_BINARIES:
        src = stage / "bin" / b
        dst = bin_dir / b
        src.replace(dst)
        dst.chmod(dst.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)

    wheels_dir = stage / "wheels"
    print("[ttc] Installing runtime dependencies ...", file=sys.stderr)
    subprocess.check_call([
        sys.executable, "-m", "pip", "install",
        "--quiet",
        "--find-links", str(wheels_dir),
        "--no-index",
        *BOOTSTRAP_WHEEL_PACKAGES,
    ])

    shutil.rmtree(extract_dir)
    print("[ttc] Setup complete.", file=sys.stderr)
    return bin_dir
