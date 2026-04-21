#!/bin/bash

set -e

die() { echo "$*" 1>&2 ; exit 1; }

if [ $# -lt 1 ]; then
    die "not enough arguments. usage: $0 <dir>"
fi

MOUNTPOINT=/mnt
LOOPDEVICE=/dev/loop0
    
echo "Resetting llvm-cov..."
echo 1 > /sys/kernel/debug/llvm-cov/reset

for f in "$1"/*.img.zst; do {
    echo "Tesing $f..."
    echo "Compiling..."
    gcc -Wall --std=gnu99 "${f%.img.zst}.c" -o "${f%.img.zst}.test"
    echo "Decompressing image..."
    unzstd "$f"
    echo "Setting up loop device..."
    losetup $LOOPDEVICE "${f%.zst}"
    echo "Mounting..."
    mount $LOOPDEVICE $MOUNTPOINT
    echo "Testing..."
    setpriv --bounding-set '-dac_override' "${f%.img.zst}.test" $MOUNTPOINT
    echo "Unmounting..."
    umount $MOUNTPOINT
    echo "Resetting loop device..."
    losetup -d $LOOPDEVICE
    echo "$f done!"
} 2>&1 | tee -a "${f%.img.zst}.log"
done

# echo "Collecting coverage info..."
# cp /sys/kernel/debug/llvm-cov/profraw "${f%.img}.profraw"
