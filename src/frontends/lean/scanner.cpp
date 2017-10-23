/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cctype>
#include <string>
#include "util/exception.h"
#include "util/name.h"
#include "util/utf8.h"
#include "library/type_context.h"
#include "library/message_builder.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parser_config.h"

namespace lean {

constexpr uchar Eof = 0xFF;

unsigned scanner::get_utf8_size(uchar c) {
    unsigned r = ::lean::get_utf8_size(c);
    if (r == 0)
        throw_exception("invalid utf-8 head character");
    return r;
}

void scanner::fetch_line() {
    m_curr_line.clear();
    if (std::getline(*m_stream, m_curr_line)) {
        m_curr_line.push_back('\n');
        m_sline++;
        m_spos  = 0;
        m_upos  = 0;
        m_curr  = m_curr_line[m_spos];
        if (m_curr == Eof) m_curr = 0;
        m_uskip = get_utf8_size(m_curr);
        m_uskip--;
    } else {
        m_last_line = true;
        m_curr      = Eof;
    }
}

void scanner::next() {
    lean_assert(m_curr != Eof);
    m_spos++;
    while (m_spos >= static_cast<int>(m_curr_line.size())) {
        if (m_last_line) {
            m_curr = Eof;
            return;
        } else {
            return fetch_line();
        }
    }
    m_curr = m_curr_line[m_spos];
    if (m_curr == Eof) m_curr = 0;
    if (m_uskip > 0) {
        if (!is_utf8_next(m_curr))
            throw_exception("invalid utf-8 sequence character");
        m_uskip--;
    } else {
        m_upos++;
        m_uskip = get_utf8_size(m_curr);
        m_uskip--;
    }
}

void scanner::check_not_eof(char const * error_msg) {
    if (curr() == Eof) throw_exception(error_msg);
}

[[ noreturn ]] void scanner::throw_exception(char const * msg) {
    pos_info pos = {m_sline, m_upos};
    while (curr() != Eof && !std::isspace(curr()))
        next();
    throw parser_exception(msg, m_stream_name.c_str(), pos);
}

static char const * g_end_error_str_msg = "unexpected end of string";
static char const * g_end_error_char_msg = "unexpected end of character";

optional<unsigned> scanner::try_hex_to_unsigned(uchar c) {
    if ('0' <= c && c <= '9')
        return optional<unsigned>(c - '0');
    else if ('a' <= c && c <= 'f')
        return optional<unsigned>(10 + c - 'a');
    else if ('A' <= c && c <= 'F')
        return optional<unsigned>(10 + c - 'A');
    else
        return optional<unsigned>();
}

unsigned scanner::hex_to_unsigned(uchar c) {
    if (auto r = try_hex_to_unsigned(c))
        return *r;
    else
        throw_exception("invalid hexadecimal digit");
}

void scanner::read_quoted_char(char const * error_msg, std::string & r) {
    lean_assert(curr() == '\\');
    next();
    check_not_eof(error_msg);
    uchar c = curr();
    if (c != '\\' && c != '\"' && c != 'n' && c != 't' && c != '\'' && c != 'x' && c != 'u')
        throw_exception("invalid escape sequence");
    if (c == 'n') {
        next();
        r += '\n';
        return;
    } else if (c == 't') {
        next();
        r += '\t';
        return;
    } else if (c == 'x') {
        next();
        c = curr();
        unsigned v = hex_to_unsigned(c);
        next();
        c = curr();
        v = 16*v + hex_to_unsigned(c);
        next();
        /* TODO(Leo): should we sign an error if v >= 128 */
        push_unicode_scalar(r, v);
        return;
    } else if (c == 'u') {
        next();
        c = curr();
        unsigned v = hex_to_unsigned(c);
        next();
        c = curr();
        v = 16*v + hex_to_unsigned(c);
        next();
        c = curr();
        v = 16*v + hex_to_unsigned(c);
        next();
        c = curr();
        v = 16*v + hex_to_unsigned(c);
        next();
        push_unicode_scalar(r, v);
        return;
    } else {
        next();
        r += c;
        return;
    }
}

token_kind scanner::read_string() {
    lean_assert(curr() == '\"');
    next();
    m_buffer.clear();
    while (true) {
        check_not_eof(g_end_error_str_msg);
        uchar c = curr();
        if (c == '\"') {
            next();
            return token_kind::String;
        } else if (c == '\\') {
            read_quoted_char(g_end_error_str_msg, m_buffer);
        } else {
            m_buffer += c;
            next();
        }
    }
}

auto scanner::read_char() -> token_kind {
    uchar c = curr();
    if (c == '\\') {
        m_buffer.clear();
        read_quoted_char(g_end_error_char_msg, m_buffer);
        if (curr() != '\'')
            throw_exception("invalid character, ' expected");
        next();
        return token_kind::Char;
    }
    if (optional<unsigned> sz = is_utf8_first_byte(c)) {
        m_buffer.clear();
        for (unsigned i = 0; i < *sz; i++) {
            m_buffer += c;
            next();
            c = curr();
        }
        if (curr() != '\'')
            throw_exception("invalid character, ' expected");
        next();
        return token_kind::Char;
    }
    throw_exception("invalid character, input stream is not encoded using UTF-8");
}

auto scanner::read_quoted_symbol() -> token_kind {
    lean_assert(curr() == '`');
    next();
    m_buffer.clear();
    bool start = true;
    bool trailing_space = false;
    while (true) {
        check_not_eof("unexpected quoted identifier");
        uchar c = curr();
        next();
        switch (c) {
            case '`':
                if (start)
                    throw_exception("unexpected end of quoted symbol");
                m_name_val = name(m_buffer.c_str());
                return token_kind::QuotedSymbol;
            case '\"':
            case '\n':
            case '\t':
                throw_exception("invalid quoted symbol, invalid character");
            case ' ':
                if (!start)
                    trailing_space = true;
                m_buffer += c;
                break;
            default:
                if (start && std::isdigit(c))
                    throw_exception("first character of a quoted symbols cannot be a digit");
                start = false;
                if (trailing_space)
                    throw_exception("unexpected space inside of quoted symbol");
                m_buffer += c;
        }
    }
}

bool scanner::is_next_digit() {
    lean_assert(curr() != Eof);
    if (m_spos + 1 < static_cast<int>(m_curr_line.size()))
        return std::isdigit(m_curr_line[m_spos+1]);
    else
        return false;
}

auto scanner::read_hex_number() -> token_kind {
    lean_assert(curr() == 'x');
    next();
    m_num_val = 0;
    bool found = false;
    while (true) {
        uchar c = curr();
        if (auto d = try_hex_to_unsigned(c)) {
            found = true;
            m_num_val = 16 * m_num_val + *d;
            next();
        } else {
            break;
        }
    }
    if (!found)
        throw exception("invalid hexadecimal numeral, hexadecimal digit expected");
    return token_kind::Decimal;
}

optional<unsigned> scanner::try_digit_to_unsigned(int base, uchar c) {
    lean_assert(base == 2 || base == 8 || base == 10 || base == 16);
    if ('0' <= c && c <= '9') {
        if (base == 2 && c >= '2')
            throw_exception("invalid binary digit");
        if (base == 8 && c >= '8')
            throw_exception("invalid octal digit");
        return optional<unsigned>(c - '0');
    } else if (base == 16 && 'a' <= c && c <= 'f') {
        return optional<unsigned>(10 + c - 'a');
    } else if (base == 16 && 'A' <= c && c <= 'F') {
        return optional<unsigned>(10 + c - 'A');
    }
    return optional<unsigned>();
}

auto scanner::read_number() -> token_kind {
    lean_assert('0' <= curr() && curr() <= '9');
    mpq q(1);
    uchar c = curr();
    next();
    m_num_val = c - '0';

    // Check for alternate base when first digit is zero.
    int base = 10;
    if (m_num_val == 0) {
        switch (curr()) {
        case 'b':
        case 'B':
            base = 2;
            next();
            break;
        case 'o':
        case 'O':
            base = 8;
            next();
            break;
        case 'x':
        case 'X':
            base = 16;
            next();
            break;
        }
        // Read digit after prefix.
        if (base != 10) {
            if (auto r = try_digit_to_unsigned(base, curr())) {
                next();
                m_num_val = *r;
            } else {
                throw_exception("invalid numeral, expected digit after base prefix");
            }
        }
    }

    bool is_post_decimal = false; // Encountered a decimal point (requires base = 10)

    while (true) {
        c = curr();
        if (auto r = try_digit_to_unsigned(base, c)) {
            m_num_val = base*m_num_val + *r;
            if (is_post_decimal)
                q *= 10;
            next();
        } else if (base == 10 && c == '.') {
            // Num. is not a decimal. It should be at least Num.0
            if (is_next_digit()) {
                if (is_post_decimal)
                    break;
                is_post_decimal = true;
                next();
            } else {
                break;
            }
        } else {
            break;
        }
    }
    if (is_post_decimal)
        m_num_val /= q;
    return is_post_decimal ? token_kind::Decimal : token_kind::Numeral;
}

void scanner::read_single_line_comment() {
    while (true) {
        if (curr() == '\n') {
            next();
            return;
        } else if (curr() == Eof) {
            return;
        } else {
            next();
        }
    }
}

void scanner::read_doc_block_core() {
    m_buffer.clear();
    while (true) {
        check_not_eof("unexpected end of documentation block");
        uchar c = curr();
        next();
        if (c == '-') {
            if (curr() == '/') {
                next();
                return;
            }
        }
        m_buffer += c;
    }
}

auto scanner::read_doc_block() -> token_kind {
    read_doc_block_core();
    return token_kind::DocBlock;
}

auto scanner::read_mod_doc_block() -> token_kind {
    read_doc_block_core();
    return token_kind::ModDocBlock;
}

void scanner::read_comment_block() {
    unsigned nesting = 1;
    while (true) {
        uchar c = curr();
        check_not_eof("unexpected end of comment block");
        next();
        if (c == '/') {
            if (curr() == '-') {
                next();
                nesting++;
            }
        } else if (c == '-') {
            if (curr() == '/') {
                next();
                nesting--;
                if (nesting == 0)
                    return;
            }
        }
    }
}

// Read until the end_str is found, store all characters (not including end_str) in m_buffer.
// Throw a parser exception error_msg if end of file is found before end_str.
void scanner::read_until(uchar const * end_str, char const * error_msg) {
    lean_assert(end_str);
    lean_assert(end_str[0]);
    m_buffer.clear();
    while (true) {
        check_not_eof(error_msg);
        uchar c = curr_next();
        if (c == end_str[0]) {
            m_aux_buffer.clear();
            m_aux_buffer += c;
            unsigned i = 1;
            while (true) {
                if (!end_str[i])
                    return;
                check_not_eof(error_msg);
                c = curr_next();
                if (c != end_str[i]) {
                    m_buffer += m_aux_buffer;
                    break;
                }
                i++;
            }
        } else {
            m_buffer += c;
        }
    }
}

void scanner::move_back(unsigned offset, unsigned u_offset) {
    lean_assert(m_uskip == 0);
    if (offset != 0) {
        if (curr() == Eof) {
            m_curr = 0;
            m_spos--;
            m_upos--;
            offset--;
            u_offset--;
        }
        if (offset != 0) {
            m_spos -= offset;
            m_upos -= u_offset;
        }
        next();
    }
}

void scanner::next_utf_core(uchar c, buffer<uchar> & cs) {
    cs.push_back(c);
    while (m_uskip > 0) {
        next();
        cs.push_back(curr());
    }
}

void scanner::next_utf(buffer<uchar> & cs) {
    next();
    next_utf_core(curr(), cs);
}

static char const * g_error_key_msg = "unexpected token";

void scanner::read_field_idx() {
    lean_assert('0' <= curr() && curr() <= '9');
    mpz q(1);
    uchar c = curr();
    next();
    m_num_val = c - '0';
    while (true) {
        c = curr();
        if (auto r = try_digit_to_unsigned(10, c)) {
            m_num_val = 10*m_num_val + *r;
            next();
        } else {
            break;
        }
    }
}

auto scanner::read_key_cmd_id() -> token_kind {
    buffer<uchar> cs;
    next_utf_core(curr(), cs);
    unsigned num_utfs  = 1;
    unsigned id_sz     = 0;
    unsigned id_utf_sz = 0;

    auto read_id_part = [&]() {
        bool escaped = false;
        while (true) {
            unsigned u = utf8_to_unicode(&cs[id_sz], cs.end());
            if (escaped) {
                if (u == id_end_escape) {
                    escaped = false;
                } else if (u == '\r' || u == '\n' || u == '\t' || u == id_begin_escape) {
                    throw_exception("illegal character in escaped identifier");
                }
            } else {
                if (u == id_begin_escape) {
                    escaped = true;
                } else if (!is_id_rest(&cs[id_sz], cs.end())) {
                    return;
                }
            }
            id_sz = cs.size();
            id_utf_sz = num_utfs;
            next_utf(cs);
            num_utfs++;
        }
    };

    auto cs_to_name = [&]() {
        name n;
        std::string & id_part = m_buffer;
        id_part.clear();
        bool escaped = false;
        for (unsigned i = 0; i < id_sz; i += get_utf8_size(cs[i])) {
            unsigned u = utf8_to_unicode(&cs[i], cs.end());
            if (u == id_begin_escape) {
                escaped = true;
            } else if (u == id_end_escape) {
                escaped = false;
            } else if (!escaped && cs[i] == '.') {
                n = name(n, id_part.c_str());
                id_part.clear();
            } else {
                id_part.append(&cs[i], &cs[i + get_utf8_size(cs[i])]);
            }
        }
        n = name(n, id_part.c_str());
        return n;
    };

    if (m_field_notation && cs[0] == '.') {
        next_utf(cs);
        num_utfs++;
        if (std::isdigit(curr())) {
            /* field notation `.` <number> */
            read_field_idx();
            return token_kind::FieldNum;
        } else {
            if (is_id_first(&cs[1], cs.end()) && cs[1] != '_') {
                /* field notation `.` <atomic_id> */
                num_utfs--;
                cs.erase(0);
                read_id_part();
                move_back(cs.size() - id_sz, 1);
                m_name_val = cs_to_name();
                return token_kind::FieldName;
            }
        }
    } else if (is_id_first(cs.begin(), cs.end())) {
        while (true) {
            read_id_part();
            if (cs[id_sz] == '.') {
                next_utf(cs);
                num_utfs++;
                if (is_id_first(&cs[id_sz + 1], cs.end())) {
                    id_sz++;
                    id_utf_sz++;
                    continue;
                }
            }
            break;
        }
    }

    unsigned i = 0;
    token_table const * it  = m_tokens;
    token_info const * info = nullptr;
    unsigned key_sz       = 0;
    unsigned key_utf_sz   = 0;
    while (i < id_sz) {
        it = find(*it, cs[i]);
        i++;
        if (!it)
            break;
        if (auto new_info = value_of(*it)) {
            lean_assert(m_uskip == 0);
            info       = new_info;
            key_sz     = i;
            key_utf_sz = id_utf_sz; // this is imprecise if key_sz < id_sz, but this case is irrelevant
        }
    }

    while (it) {
        if (i == cs.size()) {
            next_utf(cs);
            num_utfs++;
        }
        it = find(*it, cs[i]);
        i++;
        if (!it)
            break;
        if (auto new_info = value_of(*it)) {
            lean_assert(m_uskip == 0);
            info       = new_info;
            key_sz     = i;
            key_utf_sz = num_utfs;
            lean_assert(key_sz > id_sz);
        }
    }

    if (id_sz == 0 && key_sz == 0)
        throw_exception(g_error_key_msg);
    if (id_sz > key_sz) {
        move_back(cs.size() - id_sz, num_utfs - id_utf_sz);
        m_name_val = cs_to_name();
        return token_kind::Identifier;
    } else {
        move_back(cs.size() - key_sz, num_utfs - key_utf_sz);
        m_token_info = *info;
        return m_token_info.is_command() ? token_kind::CommandKeyword : token_kind::Keyword;
    }
}

static name * g_begin_comment_tk        = nullptr;
static name * g_begin_comment_block_tk  = nullptr;
static name * g_begin_doc_block_tk      = nullptr;
static name * g_begin_mod_doc_block_tk  = nullptr;
static name * g_tick_tk                 = nullptr;

void initialize_scanner() {
    g_begin_comment_tk       = new name("--");
    g_begin_comment_block_tk = new name("/-");
    g_begin_doc_block_tk     = new name("/--");
    g_begin_mod_doc_block_tk = new name("/-!");
    g_tick_tk                = new name("'");
}

void finalize_scanner() {
    delete g_begin_comment_tk;
    delete g_begin_comment_block_tk;
    delete g_begin_doc_block_tk;
    delete g_begin_mod_doc_block_tk;
    delete g_tick_tk;
}

auto scanner::scan(environment const & env) -> token_kind {
    m_tokens = &get_token_table(env);
    while (true) {
        uchar c = curr();
        m_pos  = m_upos;
        m_line = m_sline;
        switch (c) {
        case ' ': case '\r': case '\t': case '\n':
            next();
            break;
        case '\"':
            return read_string();
        case '`':
            if (m_in_notation) {
                return read_quoted_symbol();
            } else {
                return read_key_cmd_id();
            }
        case Eof:
            return token_kind::Eof;
        default:
            if (std::isdigit(c)) {
                return read_number();
            } else {
                token_kind k = read_key_cmd_id();
                if (k == token_kind::Keyword) {
                    // We treat '/-', '/--', '/-!', '--' as "keyword".
                    name const & n = m_token_info.value();
                    if (n == *g_begin_comment_tk)
                        read_single_line_comment();
                    else if (n == *g_begin_comment_block_tk)
                        read_comment_block();
                    else if (n == *g_begin_doc_block_tk)
                        return read_doc_block();
                    else if (n == *g_begin_mod_doc_block_tk)
                        return read_mod_doc_block();
                    else if (n == *g_tick_tk)
                        return read_char();
                    else
                        return k;
                } else {
                    return k;
                }
            }
        }
    }
}

scanner::scanner(std::istream & strm, char const * strm_name):
    m_tokens(nullptr), m_stream(&strm) {
    m_stream_name = strm_name ? strm_name : "[unknown]";
    m_sline = 0;
    m_spos  = 0;
    m_upos  = 0;
    m_uskip = 0;
    m_in_notation = false;
    m_last_line = false;
    fetch_line();
    if (m_sline == 0) m_sline = 1;
    m_line = m_sline;
    m_pos = 0;
    lean_assert(pos_info(get_line(), get_pos()) == pos_info(1, 0));
}

scanner::scanner(std::istream & strm, char const * strm_name, pos_info const & pos) :
        scanner(strm, strm_name) {
    skip_to_pos(pos);
}

void scanner::skip_to_pos(pos_info const & pos) {
    for (unsigned line_no = 1; line_no < pos.first; line_no++)
        fetch_line();
    m_line = m_sline;
    while (static_cast<unsigned>(m_upos) < pos.second)
        next();
    m_pos = m_upos; // we assume that the argument is the start of a token
    lean_assert(pos == pos_info(get_line(), get_pos()));
}

std::ostream & operator<<(std::ostream & out, token_kind k) {
    out << static_cast<unsigned>(k);
    return out;
}

token::token(pos_info const & p):m_kind(token_kind::Eof), m_pos(p) {}
token::token(token_kind k, pos_info const & p, token_info const & info):
    m_kind(k), m_pos(p), m_info(new token_info(info)) {
    lean_assert(m_kind == token_kind::Keyword || m_kind == token_kind::CommandKeyword);
}
token::token(token_kind k, pos_info const & p, name const & v):
    m_kind(k), m_pos(p), m_name_val(new name(v)) {
    lean_assert(m_kind == token_kind::QuotedSymbol || m_kind == token_kind::Identifier || m_kind == token_kind::FieldName);
}
token::token(token_kind k, pos_info const & p, mpq const & v):
    m_kind(k), m_pos(p), m_num_val(new mpq (v)) {
    lean_assert(m_kind == token_kind::Decimal || m_kind == token_kind::Numeral || m_kind == token_kind::FieldNum);
}

token::token(token_kind k, pos_info const & p, std::string const & v):
    m_kind(k), m_pos(p), m_str_val(new std::string(v)) {
    lean_assert(m_kind == token_kind::String || m_kind == token_kind::Char ||
                m_kind == token_kind::DocBlock || m_kind == token_kind::ModDocBlock);
}

void token::dealloc() {
    switch (kind()) {
    case token_kind::Eof:
        return;
    case token_kind::Keyword: case token_kind::CommandKeyword:
        if (m_info != nullptr) delete m_info;
        return;
    case token_kind::Identifier: case token_kind::QuotedSymbol: case token_kind::FieldName:
        if (m_name_val != nullptr) delete m_name_val;
        return;
    case token_kind::Numeral: case token_kind::Decimal: case token_kind::FieldNum:
        if (m_num_val != nullptr) delete m_num_val;
        return;
    case token_kind::String: case token_kind::Char:
    case token_kind::DocBlock: case token_kind::ModDocBlock:
        if (m_str_val != nullptr) delete m_str_val;
        return;
    }
}

void token::copy(token const & tk) {
    m_kind = tk.m_kind;
    m_pos  = tk.m_pos;
    switch (tk.kind()) {
    case token_kind::Eof:
        return;
    case token_kind::Keyword: case token_kind::CommandKeyword:
        m_info = new token_info(*tk.m_info);
        return;
    case token_kind::Identifier: case token_kind::QuotedSymbol: case token_kind::FieldName:
        m_name_val = new name(*tk.m_name_val);
        return;
    case token_kind::Numeral: case token_kind::Decimal: case token_kind::FieldNum:
        m_num_val = new mpq(*tk.m_num_val);
        return;
    case token_kind::String: case token_kind::Char:
    case token_kind::DocBlock: case token_kind::ModDocBlock:
        m_str_val = new std::string(*tk.m_str_val);
        return;
    }
}

void token::steal(token && tk) {
    m_kind = tk.m_kind;
    m_pos  = tk.m_pos;
    switch (tk.kind()) {
    case token_kind::Eof:
        return;
    case token_kind::Keyword: case token_kind::CommandKeyword:
        m_info    = tk.m_info;
        tk.m_info = nullptr;
        return;
    case token_kind::Identifier: case token_kind::QuotedSymbol: case token_kind::FieldName:
        m_name_val    = tk.m_name_val;
        tk.m_name_val = nullptr;
        return;
    case token_kind::Numeral: case token_kind::Decimal: case token_kind::FieldNum:
        m_num_val    = tk.m_num_val;
        tk.m_num_val = nullptr;
        return;
    case token_kind::String: case token_kind::Char:
    case token_kind::DocBlock: case token_kind::ModDocBlock:
        m_str_val    = tk.m_str_val;
        tk.m_str_val = nullptr;
        return;
    }
}

token read_tokens(environment & env, io_state const & ios, scanner & s, buffer<token> & tk, bool use_exceptions) {
    while (true) {
        try {
            token_kind k = s.scan(env);
            switch (k) {
            case token_kind::Eof:
                return token(s.get_pos_info());
            case token_kind::Keyword:
                tk.push_back(token(k, s.get_pos_info(), s.get_token_info()));
                break;
            case token_kind::CommandKeyword:
                if (s.get_token_info().value() == get_end_tk())
                    tk.push_back(token(k, s.get_pos_info(), s.get_token_info()));
                else
                    return token(k, s.get_pos_info(), s.get_token_info());
                break;
            case token_kind::Identifier: case token_kind::QuotedSymbol: case token_kind::FieldName:
                tk.push_back(token(k, s.get_pos_info(), s.get_name_val()));
                break;
            case token_kind::Numeral: case token_kind::Decimal: case token_kind::FieldNum:
                tk.push_back(token(k, s.get_pos_info(), s.get_num_val()));
                break;
            case token_kind::String: case token_kind::Char:
            case token_kind::DocBlock: case token_kind::ModDocBlock:
                tk.push_back(token(k, s.get_pos_info(), s.get_str_val()));
                break;
            }
        } catch (throwable & ex) {
            if (use_exceptions) {
                throw;
            } else {
                message_builder builder(env, ios, s.get_stream_name(), s.get_pos_info(), ERROR);
                builder.set_exception(ex);
                builder.report();
            }
        }
    }
}
}
