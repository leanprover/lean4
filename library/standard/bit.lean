-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
namespace bit
inductive bit : Type :=
| b0 : bit
| b1 : bit
notation `'0` := b0
notation `'1` := b1
end
