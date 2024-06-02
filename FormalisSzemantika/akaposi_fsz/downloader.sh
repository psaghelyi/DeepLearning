#!/bin/bash

wget -r -np -nH --cut-dirs=2 --mirror --convert-links --adjust-extension --page-requisites --no-parent https://people.inf.elte.hu/akaposi/fsz/

find . -type f -name '*.v.html' -exec bash -c 'for file; do mv "$file" "${file%.v.html}.v"; done' bash {} +

