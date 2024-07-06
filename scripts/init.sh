#!/usr/bin/env bash

# Initializing build environment


rustup install nightly-2021-03-01
rustup target add wasm32-unknown-unknown --toolchain nightly-2020-10-06-x86_64-unknown-linux-gnu
