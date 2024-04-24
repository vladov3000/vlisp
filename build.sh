mkdir -p build
gcc -lm -g -fsanitize=undefined code/main.c -o build/vlisp
