/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Lev Nachmanson
*/
#pragma once

// reads a text file
#include <string>
#include <vector>
#include <unordered_map>
#include <iostream>
#include <fstream>
#include <util/numerics/mpq.h>
#include "util/lp/lp_solver.h"

namespace lean {
using namespace std;

template <typename T>
struct test_result {
    lp_status m_status;
    T m_cost;
    unordered_map<string, T> column_values;
};

template <typename T>
class test_file_reader {
    struct raw_blob {
        vector<string> m_unparsed_strings;
        vector<raw_blob> m_blobs;
    };

    struct test_file_blob {
        string m_name;
        string m_content;
        unordered_map<string, string> m_table;
        unordered_map<string, test_file_blob> m_blobs;

        test_result<T> * get_test_result() {
            test_result<T> * tr = new test_result<T>();
            throw "not impl";
            return tr;
        }
    };
    ifstream m_file_stream;
public:
    // constructor
    test_file_reader(string file_name) :  m_file_stream(file_name) {
        if (!m_file_stream.is_open()) {
            cout << "cannot open file " << "\'" << file_name << "\'" << endl;
        }
    }

    raw_blob scan_to_row_blob() {
    }

    test_file_blob scan_row_blob_to_test_file_blob(raw_blob /* rblob */) {
    }

    test_result<T> * get_test_result() {
        if (!m_file_stream.is_open()) {
            return nullptr;
        }

        raw_blob rblob = scan_to_row_blob();

        test_file_blob tblob = scan_row_blob_to_test_file_blob(rblob);

        return tblob.get_test_result();
    }
};
}
