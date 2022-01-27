#!/bin/bash

mkdir -p publish
cross build --target x86_64-apple-darwin
cp target/x86_64-apple-darwin/debug/ir441 publish/ir441-macos-x64
cross build --target x86_64-unknown-linux-gnu
cp target/x86_64-unknown-linux-gnu/debug/ir441 publish/ir441-linux-x64
cross build --target x86_64-pc-windows-gnu
cp target/x86_64-pc-windows-gnu/debug/ir441.exe publish/ir441-cygwin-x64.exe