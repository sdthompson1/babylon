module ExternName

interface {}

extern function test1() = "";  // Error, empty string

extern function test2() = "!%$";  // Error, chars must be alphanumeric or underscores

extern function test3() = "1ab";  // Error, cannot start with number

extern function test4() = "_ab";  // Error, cannot start with underscore

extern function test5() = "Abc$x";  // Error, punctuation symbol "mid-string"

extern function test6() = "ab cd ef";  // Error, contains spaces

extern function test7() = "ab\x07";   // Error, control character

extern function test_ok() = "test_123";  // This is ok
