# Copyright (C) 2015-2016 Jonathan Müller <jonathanmueller.dev@gmail.com>
# This file is subject to the license terms in the LICENSE file
# found in the top-level directory of this distribution.

if(NOT COMP_API_VERSION)
    message(FATAL_ERROR "needs newer comp_base.cmake version")
endif()
comp_api_version(1)

comp_feature(sized_deallocation
        "int main()
        {
            void *ptr = 0;
            ::operator delete(ptr, 0);
        }" COMP_CPP14_FLAG)

if(COMP_API_VERSION VERSION_GREATER 1.0)
    comp_sd6_macro(sized_deallocation __cpp_sized_deallocation 201309)
endif()
