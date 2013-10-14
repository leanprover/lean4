/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Lev Nachmanson
*/

#include <unordered_map>
#include <vector>
#include <string>
#include <set>
#include <iostream>

using namespace std;
namespace lean {
class argument_parser {
    unordered_map<string, string> m_options;
    unordered_map<string, string> m_options_with_after_string;
    std::set<string> m_used_options;
    unordered_map<string, string> m_used_options_with_after_string;
    vector<string> m_free_args;
    vector<string> m_args;

public:
    string m_error_message;
    argument_parser(unsigned argn, char * const* args) {
        for (unsigned i = 0; i < argn; i++) {
            m_args.push_back(string(args[i]));
        }
    }

    void add_option(string s) {
        add_option_with_help_string(s, "");
    }

    void add_option_with_help_string(string s, string help_string) {
        m_options[s]=help_string;
    }

    void add_option_with_after_string(string s) {
        add_option_with_after_string_with_help(s, "");
    }

    void add_option_with_after_string_with_help(string s, string help_string) {
        m_options_with_after_string[s]=help_string;
    }


    bool parse() {
        bool status_is_ok = true;
        for (unsigned i = 0; i < m_args.size(); i++) {
            string ar = m_args[i];
            if (m_options.find(ar) != m_options.end() )
                m_used_options.insert(ar);
            else if (m_options_with_after_string.find(ar) != m_options_with_after_string.end()) {
                if (i == m_args.size() - 1) {
                    m_error_message = "Argument is missing after "+ar;
                    return false;
                }
                i++;
                m_used_options_with_after_string[ar] = m_args[i];
            } else {
                if (starts_with(ar, "-") || starts_with(ar, "//")) {
                    m_error_message = "Unknown option " + ar;
                    status_is_ok = false;
                }

                m_free_args.push_back(ar);
            }
        }
        return status_is_ok;
    }

    bool contains(unordered_map<string, string> & m, string s) {
        return m.find(s) != m.end();
    }

    bool contains(std::set<string> & m, string s) {
        return m.find(s) != m.end();
    }

    bool option_is_used(string option) {
        return contains(m_used_options, option) || contains(m_used_options_with_after_string, option);
    }

    string get_option_value(string option) {
        auto t = m_used_options_with_after_string.find(option);
        if (t != m_used_options_with_after_string.end()){
            return t->second;
        }
        return string();
    }

    bool starts_with(string s, char const * prefix) {
        return starts_with(s, string(prefix));
    }

    bool starts_with(string s, string prefix) {
        return s.substr(0, prefix.size()) == prefix;
    }

    string usage_string() {
        string ret = "";
        vector<string> unknown_options;
        for (auto t : m_free_args) {
            if (starts_with(t, "-") || starts_with(t, "\\")) {
                unknown_options.push_back(t);
            }
        }
        if (unknown_options.size()) {
            ret = "Unknown options:";
        }
        for (auto unknownOption : unknown_options) {
            ret += unknownOption;
            ret += ",";
        }
        ret += "\n";
        ret += "Usage:\n";
        for (auto allowed_option : m_options)
            ret += allowed_option.first + " " + (allowed_option.second.size() == 0 ? string("") : string("/") + allowed_option.second) + string("\n");
        for (auto s : m_options_with_after_string) {
            ret += s.first + " " + (s.second.size() == 0? " \"option value\"":("\""+ s.second+"\"")) + "\n";
        }
        return ret;
    }

    void print() {
        for (string s : m_used_options) {
            cout << s << endl;
        }
        for (auto & t : m_used_options_with_after_string) {
            cout << t.first << " " << t.second << endl;
        }
    }
};
}
