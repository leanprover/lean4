/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/lua_named_param.h"
#include "util/sstream.h"
#include "util/int64.h"

namespace lean {
bool get_bool_named_param(lua_State * L, int idx, char const * opt_name, bool def_value) {
    if (lua_istable(L, idx)) {
        bool result = def_value;
        push_string(L, opt_name);
        lua_gettable(L, idx);
        if (lua_isboolean(L, -1)) {
            result = lua_toboolean(L, -1);
            lua_pop(L, 1);
            return result;
        } else if (lua_isnil(L, -1)) {
            lua_pop(L, 1);
            return result;
        } else {
            lua_pop(L, 1);
            throw exception(sstream() << "field '" << opt_name << "' must be a Boolean in table at arg #" << idx);
        }
    } else if (idx <= lua_gettop(L) && !lua_isnil(L, idx)) {
        throw exception(sstream() << "arg #" << idx << " must be a table");
    } else {
        return def_value;
    }
}

int get_int_named_param(lua_State * L, int idx, char const * opt_name, int def_value) {
    if (lua_istable(L, idx)) {
        int result = def_value;
        push_string(L, opt_name);
        lua_gettable(L, idx);
        if (lua_isnumber(L, -1)) {
            result = lua_tointeger(L, -1);
            lua_pop(L, 1);
            return result;
        } else if (lua_isnil(L, -1)) {
            lua_pop(L, 1);
            return result;
        } else {
            lua_pop(L, 1);
            throw exception(sstream() << "field '" << opt_name << "' must be an integer in table at arg #" << idx);
        }
    } else if (idx <= lua_gettop(L) && !lua_isnil(L, idx)) {
        throw exception(sstream() << "arg #" << idx << " must be a table");
    } else {
        return def_value;
    }
}

unsigned get_uint_named_param(lua_State * L, int idx, char const * opt_name, unsigned def_value) {
    if (lua_istable(L, idx)) {
        push_string(L, opt_name);
        lua_gettable(L, idx);
        if (lua_isnumber(L, -1)) {
            int64 result = lua_tointeger(L, -1);
            lua_pop(L, 1);
            if (result < 0 || result > static_cast<int64>(std::numeric_limits<unsigned>::max()))
                throw exception(sstream() << "field '" << opt_name << "' must be a unsigned integer in table at arg #" << idx);
            return static_cast<unsigned>(result);
        } else if (lua_isnil(L, -1)) {
            lua_pop(L, 1);
            return def_value;
        } else {
            lua_pop(L, 1);
            throw exception(sstream() << "field '" << opt_name << "' must be a unsigned integer in table at arg #" << idx);
        }
    } else if (idx <= lua_gettop(L) && !lua_isnil(L, idx)) {
        throw exception(sstream() << "arg #" << idx << " must be a table");
    } else {
        return def_value;
    }
}

optional<unsigned> get_opt_uint_named_param(lua_State * L, int idx, char const * opt_name, optional<unsigned> const & def_value) {
    if (lua_istable(L, idx)) {
        push_string(L, opt_name);
        lua_gettable(L, idx);
        if (lua_isnumber(L, -1)) {
            int64 result = lua_tointeger(L, -1);
            lua_pop(L, 1);
            if (result < 0 || result > static_cast<int64>(std::numeric_limits<unsigned>::max()))
                throw exception(sstream() << "field '" << opt_name << "' must be a unsigned integer in table at arg #" << idx);
            return optional<unsigned>(static_cast<unsigned>(result));
        } else if (lua_isnil(L, -1)) {
            lua_pop(L, 1);
            return def_value;
        } else {
            lua_pop(L, 1);
            throw exception(sstream() << "field '" << opt_name << "' must be a unsigned integer in table at arg #" << idx);
        }
    } else if (idx <= lua_gettop(L) && !lua_isnil(L, idx)) {
        throw exception(sstream() << "arg #" << idx << " must be a table");
    } else {
        return def_value;
    }
}

name_set get_name_set_named_param(lua_State * L, int idx, char const * opt_name, name_set const & def_value) {
    if (lua_istable(L, idx)) {
        push_string(L, opt_name);
        lua_gettable(L, idx);
        if (is_name_set(L, -1)) {
            name_set result = to_name_set(L, -1);
            lua_pop(L, 1);
            return result;
        } else if (lua_isnil(L, -1)) {
            lua_pop(L, 1);
            return def_value;
        } else {
            lua_pop(L, 1);
            throw exception(sstream() << "field '" << opt_name << "' must be a name_set in table at arg #" << idx);
        }
    } else if (idx <= lua_gettop(L) && !lua_isnil(L, idx)) {
        throw exception(sstream() << "arg #" << idx << " must be a table");
    } else {
        return def_value;
    }
}

list<name> get_list_name_named_param(lua_State * L, int idx, char const * opt_name, list<name> const & def_value) {
    if (lua_istable(L, idx)) {
        push_string(L, opt_name);
        lua_gettable(L, idx);
        if (is_list_name(L, -1) || lua_istable(L, -1)) {
            list<name> result = to_list_name_ext(L, -1);
            lua_pop(L, 1);
            return result;
        } else if (lua_isnil(L, -1)) {
            lua_pop(L, 1);
            return def_value;
        } else {
            lua_pop(L, 1);
            throw exception(sstream() << "field '" << opt_name << "' must be a list of names in table at arg #" << idx);
        }
    } else if (idx <= lua_gettop(L) && !lua_isnil(L, idx)) {
        throw exception(sstream() << "arg #" << idx << " must be a table");
    } else {
        return def_value;
    }
}
}

