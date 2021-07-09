#!/bin/bash

set -e

script_path="$(dirname "$0")"
src_dir="$(dirname "$script_path")"
cd "$src_dir"

build_platform () {
  echo "Building $1"
  rm -rf dist/$1
  DOCKER_BUILDKIT=1 docker build --progress=plain -o dist/$1 -f ./build-scripts/Dockerfile.$1 .
}

case $DIST_TARGET_FILTER in
  (*[![:blank:]]*)
    case $DIST_TARGET_FILTER in
      linux-x64)      build_platform linux-x64 ;;
      linux-musl-x64) build_platform linux-musl-x64 ;;
      linux-armv7)    build_platform linux-armv7 ;;
      linux-arm64)    build_platform linux-arm64 ;;
      windows-x64)    build_platform windows-x64 ;;
      macos-x64)      build_platform macos-x64 ;;
      macos-arm64)    build_platform macos-arm64 ;;
      *)
        echo "Invalid dist target filter '$DIST_TARGET_FILTER'"
        exit 1
        ;;
    esac
    ;;
  (*)
    echo "Building distrubtions for all targets."
    build_platform linux-x64
    build_platform linux-musl-x64
    build_platform linux-armv7
    build_platform linux-arm64
    build_platform windows-x64
    build_platform macos-x64
    build_platform macos-arm64
    ;;
esac
