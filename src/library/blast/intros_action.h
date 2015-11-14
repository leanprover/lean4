/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
namespace blast {
/** \brief Introduce upto \c max hypotheses.
    Return false if there is nothing to introduce, that is, target is not a Pi-type. */
bool intros_action(unsigned max);
/** \brief Keep introducing until target is not a Pi-type. */
bool intros_action();
}}
