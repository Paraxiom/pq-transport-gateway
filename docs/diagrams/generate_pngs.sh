#!/bin/bash
# Generate PNG images from DOT files

echo "Generating PNG diagrams..."

# Check if dot is installed
if ! command -v dot &> /dev/null; then
    echo "Graphviz not installed. Install with: sudo apt-get install graphviz"
    exit 1
fi

# Convert each .dot file to .png
for dotfile in *.dot; do
    if [ -f "$dotfile" ]; then
        pngfile="${dotfile%.dot}.png"
        echo "Converting $dotfile -> $pngfile"
        dot -Tpng "$dotfile" -o "$pngfile"
    fi
done

echo "Done! PNG files generated."
ls -la *.png