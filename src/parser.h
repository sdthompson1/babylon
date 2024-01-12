/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef PARSER_H
#define PARSER_H

// Returns NULL on parse error.

// The returned module must be freed using free_module.

struct Module * parse_module(const struct Token * token, bool interface_only);

#endif
