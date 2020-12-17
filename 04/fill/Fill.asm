// This file is part of www.nand2tetris.org
// and the book "The Elements of Computing Systems"
// by Nisan and Schocken, MIT Press.
// File name: projects/04/Fill.asm

// Runs an infinite loop that listens to the keyboard input.
// When a key is pressed (any key), the program blackens the screen,
// i.e. writes "black" in every pixel;
// the screen should remain fully black as long as the key is pressed. 
// When no key is pressed, the program clears the screen, i.e. writes
// "white" in every pixel;
// the screen should remain fully clear as long as no key is pressed.

// Put your code here.

// Fill

(MAIN)
@KBD
D=M

@REL
D;JEQ

@0
D=!A
@R0
M=D
@CALL
0;JMP

(REL)
@0
D=A
@R0
M=D

(CALL)
@MAIN
D=A
@R1
M=D
@FILL
0;JMP



(FILL)
@8191
D=A
@i
M=D

(FILL_LOOP)
@SCREEN
D=A
@i
D=D+M
@addr
M=D
@R0
D=M
@addr
A=M
M=D
@i
D=M
@END_FILL_LOOP
D;JEQ
@i
M=M-1
@FILL_LOOP
0;JMP

(END_FILL_LOOP)
@R1
A=M
0;JMP