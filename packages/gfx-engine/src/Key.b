module Key

interface {
    datatype Key =

    // Numbers
      Key_0
    | Key_1
    | Key_2
    | Key_3
    | Key_4
    | Key_5
    | Key_6
    | Key_7
    | Key_8
    | Key_9

    // Letters
    | Key_A
    | Key_B
    | Key_C
    | Key_D
    | Key_E
    | Key_F
    | Key_G
    | Key_H
    | Key_I
    | Key_J
    | Key_K
    | Key_L
    | Key_M
    | Key_N
    | Key_O
    | Key_P
    | Key_Q
    | Key_R
    | Key_S
    | Key_T
    | Key_U
    | Key_V
    | Key_W
    | Key_X
    | Key_Y
    | Key_Z

    // Space, Return etc
    | Key_Space
    | Key_Return
    | Key_Backspace
    | Key_Delete
    | Key_Tab

    // Modifier keys
    | Key_Left_Shift
    | Key_Right_Shift

    // Arrow keys
    | Key_Up
    | Key_Down
    | Key_Left
    | Key_Right

    // Function keys and Escape
    | Key_Escape
    | Key_F1
    | Key_F2
    | Key_F3
    | Key_F4
    | Key_F5
    | Key_F6
    | Key_F7
    | Key_F8
    | Key_F9
    | Key_F10
    | Key_F11
    | Key_F12;
}
