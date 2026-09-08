# This fork built as a single Lean toolchain package, laid out the way elan
# expects (bin/{lean,lake,leanc,clang}, lib/lean/...).
#
# Adapted from nixpkgs' pkgs/by-name/le/lean4/package.nix: `src` and `version`
# are parameters (the flake passes `self`), and `clang` is symlinked into
# bin/ so `lake build` finds a C compiler under `elan run` (Lake resolves it as
# <sysroot>/bin/clang, and `elan run` does not add the toolchain bin/ to PATH).
{
  lib,
  stdenv,
  cmake,
  cctools,
  fetchFromGitHub,
  git,
  gmp,
  cadical,
  clang,
  leangz,
  makeWrapper,
  pkg-config,
  libuv,
  perl,

  src,
  version,
  githash ? version,
  elanName ? "lean-${version}",
  enableMimalloc ? true,
}:

let
  cadical' = cadical.override { version = "2.1.3"; };
in
stdenv.mkDerivation (finalAttrs: {
  pname = "lean4-toolchain";
  inherit src version;

  # Vendored to match the version Lean expects exactly (perf-sensitive).
  mimalloc-src = fetchFromGitHub {
    owner = "microsoft";
    repo = "mimalloc";
    tag = "v2.2.3";
    hash = "sha256-B0gngv16WFLBtrtG5NqA2m5e95bYVcQraeITcOX9A74=";
  };

  patches = [ ./mimalloc.patch ];

  postPatch =
    let
      pattern = "\${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc";
    in
    ''
      substituteInPlace src/CMakeLists.txt \
        --replace-fail 'set(GIT_SHA1 "")' 'set(GIT_SHA1 "${githash}")'

      # Expects sourceRoot to be a git repository.
      rm -rf src/lake/examples/git/
    ''
    + lib.optionalString enableMimalloc ''
      substituteInPlace CMakeLists.txt \
        --replace-fail 'MIMALLOC-SRC' '${finalAttrs.mimalloc-src}'
      for file in stage0/src/CMakeLists.txt stage0/src/runtime/CMakeLists.txt src/CMakeLists.txt src/runtime/CMakeLists.txt; do
        substituteInPlace "$file" \
          --replace-fail '${pattern}' '${finalAttrs.mimalloc-src}'
      done
    '';

  preConfigure = ''
    patchShebangs stage0/src/bin/ src/bin/
  '';

  nativeBuildInputs = [
    cmake
    pkg-config
    makeWrapper
    leangz # provides leantar
  ]
  ++ lib.optionals stdenv.hostPlatform.isDarwin [ cctools.libtool ];

  buildInputs = [
    gmp
    libuv
    cadical'
  ];

  cmakeFlags = [
    "-DUSE_GITHASH=OFF"
    "-DINSTALL_LICENSE=OFF"
    "-DINSTALL_CADICAL=OFF"
    "-DUSE_MIMALLOC=${if enableMimalloc then "ON" else "OFF"}"
  ];

  doCheck = false;
  nativeCheckInputs = [
    git
    perl
  ];

  postInstall = ''
    wrapProgram $out/bin/lean --prefix PATH : ${cadical'}/bin
    ln -s ${lib.getExe' clang "clang"} $out/bin/clang
  '';

  passthru = { inherit elanName; };

  meta = {
    description = "Lean 4 (semantic-highlighting fork) as an elan toolchain";
    homepage = "https://github.com/leanprover/lean4";
    license = lib.licenses.asl20;
    platforms = lib.platforms.unix;
    mainProgram = "lean";
  };
})
