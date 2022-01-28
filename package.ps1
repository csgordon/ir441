#!/usr/bin/env pwsh

rustup target add x86_64-apple-darwin
rustup target add x86_64-pc-windows-gnu
rustup target add x86_64-unknown-linux-gnu
rustup target add x86_64-pc-windows-msvc

mkdir -p publish
cargo build
cp target/debug/ir441.exe publish/ir442-win-x64.exe
cross build --target x86_64-apple-darwin
cp target/x86_64-apple-darwin/debug/ir441 publish/ir441-macos-x64
cross build --target x86_64-unknown-linux-gnu
cp target/x86_64-unknown-linux-gnu/debug/ir441 publish/ir441-linux-x64
cross build --target x86_64-pc-windows-gnu
cp target/x86_64-pc-windows-gnu/debug/ir441.exe publish/ir441-cygwin-x64.exe