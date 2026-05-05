#!/usr/bin/env bash
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN_DIR="$SCRIPT_DIR/bin"
DEPS_DIR="$BIN_DIR/deps"
NPROC=10
FORCE=0

for arg in "$@"; do
  [[ "$arg" == "--force" ]] && FORCE=1
done

need_build() {
  local bin="$BIN_DIR/$1"
  [[ "$FORCE" == 1 ]] && return 0
  [[ -e "$bin" ]] && echo "  -> $1 already exists, skipping (use --force to rebuild)" && return 1
  return 0
}

echo "=== Initializing submodules ==="
git -C "$SCRIPT_DIR" submodule update --init --recursive

echo ""
echo "=== Building dependencies ==="

# --- cddlib (GMP version) ---
CDDLIB_SRC="$DEPS_DIR/cddlib"
CDDLIB_PREFIX="$CDDLIB_SRC/install"
CDDLIB_LIB="$CDDLIB_PREFIX/lib/libcddgmp.a"
if [[ "$FORCE" == 1 ]] || [[ ! -f "$CDDLIB_LIB" ]]; then
  echo ""
  echo "--- Building cddlib (GMP version) ---"
  # Remove MSVC-only AX_CHECK_COMPILE_FLAG block (not in system m4 macros)
  sed -i.bak '/AX_CHECK_COMPILE_FLAG/d' "$CDDLIB_SRC/configure.ac"
  GMP_PREFIX=$(brew --prefix gmp 2>/dev/null || echo "")
  (cd "$CDDLIB_SRC" && autoreconf -i && \
    ./configure --prefix="$CDDLIB_PREFIX" \
      ${GMP_PREFIX:+CPPFLAGS="-I$GMP_PREFIX/include"} \
      ${GMP_PREFIX:+LDFLAGS="-L$GMP_PREFIX/lib"} && \
    make -j"$NPROC" SUBDIRS="lib-src src" && \
    make install SUBDIRS="lib-src src")
  echo "  -> cddlib installed to $CDDLIB_PREFIX"
else
  echo "  -> cddlib already built, skipping"
fi

# Ensure all lib-src headers are present (macOS autoreconf can miss some)
mkdir -p "$CDDLIB_PREFIX/include/cddlib"
find "$CDDLIB_SRC/lib-src" -maxdepth 1 -name "*.h" \
  -exec install -m 644 {} "$CDDLIB_PREFIX/include/cddlib/" \;

# VolEsti includes "cdd/setoper.h"; cddlib installs under cddlib/ — add alias
ln -sf "$CDDLIB_PREFIX/include/cddlib" "$CDDLIB_PREFIX/include/cdd"

# --- VolEsti (examples/volume) ---
if need_build volume || need_build sample; then
  echo ""
  echo "--- Building VolEsti (volume + sample) ---"
  VOLESTI_SRC="$DEPS_DIR/VolEsti/examples/volume"
  VOLESTI_BUILD="$VOLESTI_SRC/build"
  LPSOLVE_DEPS="$DEPS_DIR/VolEsti/external/_deps"

  # Pre-download lp_solve so cmake FetchContent finds it locally (SourceForge hangs in cmake)
  LPSOLVE_SRC="$LPSOLVE_DEPS/lpsolve-src"
  if [[ ! -f "$LPSOLVE_SRC/lpsolve.h" ]]; then
    echo "  -> Downloading lp_solve 5.5.2.14..."
    mkdir -p "$LPSOLVE_SRC"
    curl -fsSL --max-time 120 \
      "https://github.com/lp-solve/lp_solve/releases/download/5.5.2.14/lp_solve_5.5.2.14_source.tar.gz" \
      | tar xz --strip-components=1 -C "$LPSOLVE_SRC"
  fi

  # VolEsti forces fully static executables in this example. Apple ld does not
  # support that mode, and linking fails with "library 'crt0.o' not found".
  if [[ "$(uname)" == "Darwin" ]] && \
     grep -q 'set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")' "$VOLESTI_SRC/CMakeLists.txt"; then
    echo "  -> Disabling unsupported static executable link flag on macOS"
    perl -0pi -e 's@set\(CMAKE_EXE_LINKER_FLAGS "\$\{CMAKE_EXE_LINKER_FLAGS\} -static"\)@if(NOT APPLE)\n  set(CMAKE_EXE_LINKER_FLAGS "\$\{CMAKE_EXE_LINKER_FLAGS\} -static")\nendif()@' \
      "$VOLESTI_SRC/CMakeLists.txt"
  fi

  # Clean stale build dir if lp_solve wasn't seeded in the previous run
  if [[ -d "$VOLESTI_BUILD" ]] && \
     grep -q "FATAL_ERROR\|lpsolve failed" "$VOLESTI_BUILD/CMakeFiles/CMakeError.log" 2>/dev/null; then
    echo "  -> Cleaning stale VolEsti build dir"
    rm -rf "$VOLESTI_BUILD"
  fi

  # lp_solve 5.5.2.14 bundles setoper symbols that also appear in libcdd.a;
  # allow-multiple-definition picks the first (lp_solve's compatible copy)
  ALLOW_MULTI=""
  [[ "$(uname)" == "Linux" ]] && ALLOW_MULTI="-Wl,--allow-multiple-definition"

  mkdir -p "$VOLESTI_BUILD"
  cmake -S "$VOLESTI_SRC" -B "$VOLESTI_BUILD" -DCMAKE_BUILD_TYPE=Release -Wno-dev \
    -DCDDLIB="$CDDLIB_LIB" \
    -DCMAKE_CXX_FLAGS="-I$CDDLIB_PREFIX/include" \
    -DCMAKE_C_FLAGS="-I$CDDLIB_PREFIX/include" \
    -DCMAKE_EXE_LINKER_FLAGS="$ALLOW_MULTI"
  cmake --build "$VOLESTI_BUILD" -j"$NPROC"
  install -m 755 "$VOLESTI_BUILD/volume" "$BIN_DIR/volume"
  install -m 755 "$VOLESTI_BUILD/sample" "$BIN_DIR/sample"
  echo "  -> volume, sample copied to bin/"
fi

# --- allsat-circuits (hall_tool) ---
if need_build hall_tool; then
  echo ""
  echo "--- Building allsat-circuits (hall_tool) ---"
  ALLSAT_SRC="$DEPS_DIR/allsat-circuits"
  ALLSAT_BUILD="$ALLSAT_SRC/build"
  ALLSAT_CMAKE_ARGS=(-DCMAKE_BUILD_TYPE=Release)
  git -C "$ALLSAT_SRC" submodule update --init --recursive
  mkdir -p "$ALLSAT_BUILD"

  # CMake 4 drops compatibility with projects that still declare
  # cmake_minimum_required(VERSION < 3.5) in nested subdirectories like lorina.
  if cmake --version | head -n1 | grep -Eq 'version (4|[5-9])\.'; then
    ALLSAT_CMAKE_ARGS+=(-DCMAKE_POLICY_VERSION_MINIMUM=3.5)
  fi

  # Link hall_tool as a fully static executable on Linux. Apple ld does not
  # support -static (no libc.a shipped), so skip on macOS.
  if [[ "$(uname)" != "Darwin" ]]; then
    ALLSAT_CMAKE_ARGS+=(-DCMAKE_EXE_LINKER_FLAGS=-static)
  fi

  cmake -S "$ALLSAT_SRC" -B "$ALLSAT_BUILD" "${ALLSAT_CMAKE_ARGS[@]}"
  cmake --build "$ALLSAT_BUILD" -j"$NPROC"
  install -m 755 "$ALLSAT_BUILD/hall_tool" "$BIN_DIR/hall_tool"
  echo "  -> hall_tool copied to bin/"
fi



# --- upstream-lrslib (lrs) ---
if need_build lrs; then
  echo ""
  echo "--- Building upstream-lrslib (lrs) ---"
  LRS_DIR="$DEPS_DIR/upstream-lrslib"
  LRS_CONFIGURE_ENV=()
  # lrslong.c / lrsgmp.c / lrsmp.c live in lrsarith-011/ but Makefile.am expects them at root
  for f in lrslong.c lrslong.h lrsgmp.c lrsgmp.h lrsmp.c lrsmp.h; do
    [[ -e "$LRS_DIR/$f" ]] || ln -s "lrsarith-011/$f" "$LRS_DIR/$f"
  done

  if [[ "$(uname)" == "Darwin" ]]; then
    # Apple clang enforces the signal(2) callback signature; this vendored
    # lrslib release still declares zero-argument handlers.
    if grep -q 'static void checkpoint ();' "$LRS_DIR/lrslib.c"; then
      echo "  -> Patching lrslib signal handlers for macOS"
      perl -0pi -e 's@static void checkpoint \(\);\nstatic void die_gracefully \(\);\nstatic void setup_signals \(void\);\nstatic void timecheck \(\);@static void checkpoint (int signum);\nstatic void die_gracefully (int signum);\nstatic void setup_signals (void);\nstatic void timecheck (int signum);@' \
        "$LRS_DIR/lrslib.c"
      perl -0pi -e 's@static void\ntimecheck \(\)\n\{@static void\ntimecheck (int signum)\n{\n  (void) signum;@' \
        "$LRS_DIR/lrslib.c"
      perl -0pi -e 's@static void\ncheckpoint \(\)\n\{@static void\ncheckpoint (int signum)\n{\n  (void) signum;@' \
        "$LRS_DIR/lrslib.c"
      perl -0pi -e 's@static void\ndie_gracefully \(\)\n\{@static void\ndie_gracefully (int signum)\n{\n  (void) signum;@' \
        "$LRS_DIR/lrslib.c"
    fi

    GMP_PREFIX=$(brew --prefix gmp 2>/dev/null || echo "")
    if [[ -n "$GMP_PREFIX" ]]; then
      LRS_CONFIGURE_ENV+=(
        "GMP_CFLAGS=-I$GMP_PREFIX/include"
        "GMP_LDFLAGS=-L$GMP_PREFIX/lib"
        "CPPFLAGS=-I$GMP_PREFIX/include"
        "LDFLAGS=-L$GMP_PREFIX/lib"
      )
    fi
  fi

  # Upstream builds lrs against liblrs.la, which yields a libtool wrapper
  # script at the top level and a dynamically linked binary in .libs/.
  # Link lrs against the static archives directly so bin/lrs is a real
  # executable; on Linux also request a fully static link.
  if grep -q '^lrs_LDADD = liblrs\.la ' "$LRS_DIR/Makefile.am"; then
    echo "  -> Patching lrslib lrs target to build a direct executable"
    perl -0pi -e 's@lrs_SOURCES = lrs\.c\nlrs_CPPFLAGS = -DMA \$\(GMP_CFLAGS\)\nlrs_LDADD = liblrs\.la \$\(GMP_LDFLAGS\) -lgmp@lrs_SOURCES = lrs.c lrsdriver.c\nlrs_CPPFLAGS = -DMA \$\(GMP_CFLAGS\)\nlrs_DEPENDENCIES = liblrs1.la liblrsgmp.la\nlrs_LDADD = ./.libs/liblrs1.a ./.libs/liblrsgmp.a \$\(GMP_LDFLAGS\) -lgmp@' \
      "$LRS_DIR/Makefile.am"
  fi

  if [[ "$(uname)" != "Darwin" ]] && ! grep -q '^lrs_LDFLAGS = -all-static$' "$LRS_DIR/Makefile.am"; then
    echo "  -> Enabling static link for lrslib lrs on Linux"
    perl -0pi -e 's@lrs_LDADD = \$\(GMP_LDFLAGS\) -lgmp@lrs_LDFLAGS = -all-static\nlrs_LDADD = \$\(GMP_LDFLAGS\) -lgmp@' \
      "$LRS_DIR/Makefile.am"
  fi

  (cd "$LRS_DIR" && autoreconf -i && env "${LRS_CONFIGURE_ENV[@]}" ./configure && env "${LRS_CONFIGURE_ENV[@]}" make -j"$NPROC" lrs)
  install -m 755 "$LRS_DIR/lrs" "$BIN_DIR/lrs"
  echo "  -> lrs copied to bin/"
fi

# --- pact / cvc5 ---
if need_build cvc5; then
  echo ""
  echo "--- Building pact (cvc5) ---"
  PACT_DIR="$DEPS_DIR/pact"
  PACT_BUILD="$PACT_DIR/build"
  PACT_CONFIGURE_ARGS=(--auto-download --tracing --static)

  if cmake --version | head -n1 | grep -Eq 'version (4|[5-9])\.'; then
    PACT_CONFIGURE_ARGS+=(-DCMAKE_POLICY_VERSION_MINIMUM=3.5)
  fi

  # Older cached cvc5/pact build trees may have generated a CaDiCaL external
  # project that still tries to configure the downloaded dependency with CMake,
  # which fails under CMake 4. Force a clean reconfigure in that case.
  if [[ -f "$PACT_BUILD/deps/tmp/CaDiCaL-EP-cfgcmd.txt" ]] && \
     ! grep -q 'makefile\.in' "$PACT_BUILD/deps/tmp/CaDiCaL-EP-cfgcmd.txt"; then
    echo "  -> Removing stale pact build dir with outdated CaDiCaL configure rules"
    rm -rf "$PACT_BUILD"
  fi

  (cd "$PACT_DIR" && ./configure.sh "${PACT_CONFIGURE_ARGS[@]}")
  make -j"$NPROC" -C "$PACT_BUILD"
  install -m 755 "$PACT_BUILD/bin/cvc5" "$BIN_DIR/cvc5"
  echo "  -> cvc5 copied to bin/"
fi

echo ""
echo "=== All dependencies built successfully ==="
