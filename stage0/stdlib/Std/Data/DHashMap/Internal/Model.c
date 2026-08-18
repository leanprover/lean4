// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Model
// Imports: public import Std.Data.DHashMap.Basic import all Std.Data.DHashMap.Internal.Defs public import Std.Data.DHashMap.Internal.HashesTo public import Std.Data.DHashMap.Internal.AssocList.Lemmas import Init.Data.List.Impl
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_noption_none();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_m_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
lean_object* v___y_7_; lean_object* v_i_8_; lean_object* v___y_24_; lean_object* v_i_25_; lean_object* v___y_31_; lean_object* v___x_40_; 
lean_inc(v_a_4_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v___x_40_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1_, v_inst_2_, v_m_3_, v_a_4_);
switch(lean_obj_tag(v___x_40_))
{
case 0:
{
lean_object* v_index_41_; lean_object* v_size_42_; lean_object* v___x_43_; 
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v_index_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_index_41_);
lean_dec_ref_known(v___x_40_, 3);
v_size_42_ = lean_ctor_get(v_m_3_, 0);
lean_inc(v_size_42_);
v___x_43_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3_, v_size_42_, v_index_41_, v_a_4_, v_b_5_);
lean_dec(v_index_41_);
return v___x_43_;
}
case 1:
{
lean_object* v_index_44_; lean_object* v_size_45_; lean_object* v_keyArray_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_index_44_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_index_44_);
lean_dec_ref_known(v___x_40_, 1);
v_size_45_ = lean_ctor_get(v_m_3_, 0);
v_keyArray_46_ = lean_ctor_get(v_m_3_, 1);
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_size_45_, v___x_47_);
v___x_49_ = lean_array_get_size(v_keyArray_46_);
v___x_50_ = lean_nat_dec_lt(v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
lean_dec(v___x_48_);
lean_dec(v_index_44_);
goto v___jp_13_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_51_ = lean_unsigned_to_nat(4u);
v___x_52_ = lean_nat_mul(v___x_48_, v___x_51_);
v___x_53_ = lean_unsigned_to_nat(3u);
v___x_54_ = lean_nat_mul(v___x_49_, v___x_53_);
v___x_55_ = lean_nat_dec_le(v___x_52_, v___x_54_);
lean_dec(v___x_54_);
lean_dec(v___x_52_);
if (v___x_55_ == 0)
{
lean_dec(v___x_48_);
lean_dec(v_index_44_);
goto v___jp_13_;
}
else
{
lean_object* v___x_56_; 
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_56_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_3_, v___x_48_, v_index_44_, v_a_4_, v_b_5_);
lean_dec(v_index_44_);
return v___x_56_;
}
}
}
default: 
{
lean_object* v_size_57_; lean_object* v_keyArray_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_size_57_ = lean_ctor_get(v_m_3_, 0);
v_keyArray_58_ = lean_ctor_get(v_m_3_, 1);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_size_57_, v___x_59_);
v___x_61_ = lean_array_get_size(v_keyArray_58_);
v___x_62_ = lean_nat_dec_lt(v___x_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec(v___x_60_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v___x_63_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1_, v_inst_2_, v_m_3_);
v___y_31_ = v___x_63_;
goto v___jp_30_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_64_ = lean_unsigned_to_nat(4u);
v___x_65_ = lean_nat_mul(v___x_60_, v___x_64_);
lean_dec(v___x_60_);
v___x_66_ = lean_unsigned_to_nat(3u);
v___x_67_ = lean_nat_mul(v___x_61_, v___x_66_);
v___x_68_ = lean_nat_dec_le(v___x_65_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_65_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1_, v_inst_2_, v_m_3_);
v___y_31_ = v___x_69_;
goto v___jp_30_;
}
else
{
v___y_31_ = v_m_3_;
goto v___jp_30_;
}
}
}
}
v___jp_6_:
{
lean_object* v_size_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_size_9_ = lean_ctor_get(v___y_7_, 0);
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_size_9_, v___x_10_);
v___x_12_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_7_, v___x_11_, v_i_8_, v_a_4_, v_b_5_);
lean_dec(v_i_8_);
return v___x_12_;
}
v___jp_13_:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v___x_14_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1_, v_inst_2_, v_m_3_);
lean_inc(v_a_4_);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1_, v_inst_2_, v___x_14_, v_a_4_);
switch(lean_obj_tag(v___x_15_))
{
case 0:
{
lean_object* v_index_16_; lean_object* v_size_17_; lean_object* v___x_18_; 
v_index_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_index_16_);
lean_dec_ref_known(v___x_15_, 3);
v_size_17_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_size_17_);
v___x_18_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_14_, v_size_17_, v_index_16_, v_a_4_, v_b_5_);
lean_dec(v_index_16_);
return v___x_18_;
}
case 1:
{
lean_object* v_index_19_; 
v_index_19_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_index_19_);
lean_dec_ref_known(v___x_15_, 1);
v___y_7_ = v___x_14_;
v_i_8_ = v_index_19_;
goto v___jp_6_;
}
default: 
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_14_, v___x_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_index_22_; 
v_index_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_index_22_);
lean_dec_ref_known(v___x_21_, 1);
v___y_7_ = v___x_14_;
v_i_8_ = v_index_22_;
goto v___jp_6_;
}
else
{
lean_dec(v_b_5_);
lean_dec(v_a_4_);
return v___x_14_;
}
}
}
}
v___jp_23_:
{
lean_object* v_size_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_size_26_ = lean_ctor_get(v___y_24_, 0);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_size_26_, v___x_27_);
v___x_29_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_24_, v___x_28_, v_i_25_, v_a_4_, v_b_5_);
lean_dec(v_i_25_);
return v___x_29_;
}
v___jp_30_:
{
lean_object* v___x_32_; 
lean_inc(v_a_4_);
v___x_32_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1_, v_inst_2_, v___y_31_, v_a_4_);
switch(lean_obj_tag(v___x_32_))
{
case 0:
{
lean_object* v_index_33_; lean_object* v_size_34_; lean_object* v___x_35_; 
v_index_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_index_33_);
lean_dec_ref_known(v___x_32_, 3);
v_size_34_ = lean_ctor_get(v___y_31_, 0);
lean_inc(v_size_34_);
v___x_35_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_31_, v_size_34_, v_index_33_, v_a_4_, v_b_5_);
lean_dec(v_index_33_);
return v___x_35_;
}
case 1:
{
lean_object* v_index_36_; 
v_index_36_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_index_36_);
lean_dec_ref_known(v___x_32_, 1);
v___y_24_ = v___y_31_;
v_i_25_ = v_index_36_;
goto v___jp_23_;
}
default: 
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_31_, v___x_37_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_index_39_; 
v_index_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_index_39_);
lean_dec_ref_known(v___x_38_, 1);
v___y_24_ = v___y_31_;
v_i_25_ = v_index_39_;
goto v___jp_23_;
}
else
{
lean_dec(v_b_5_);
lean_dec(v_a_4_);
return v___y_31_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_m_74_, lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(v_inst_72_, v_inst_73_, v_m_74_, v_a_75_, v_b_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_m_80_, lean_object* v_a_81_, lean_object* v_b_82_){
_start:
{
lean_object* v___y_84_; lean_object* v_i_85_; lean_object* v___y_101_; lean_object* v_i_102_; lean_object* v___y_108_; lean_object* v___x_117_; 
lean_inc(v_a_81_);
lean_inc_ref(v_inst_79_);
lean_inc_ref(v_inst_78_);
v___x_117_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_78_, v_inst_79_, v_m_80_, v_a_81_);
switch(lean_obj_tag(v___x_117_))
{
case 0:
{
lean_object* v_index_118_; lean_object* v_size_119_; lean_object* v___x_120_; 
lean_dec_ref(v_inst_79_);
lean_dec_ref(v_inst_78_);
v_index_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_index_118_);
lean_dec_ref_known(v___x_117_, 3);
v_size_119_ = lean_ctor_get(v_m_80_, 0);
lean_inc(v_size_119_);
v___x_120_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_80_, v_size_119_, v_index_118_, v_a_81_, v_b_82_);
lean_dec(v_index_118_);
return v___x_120_;
}
case 1:
{
lean_object* v_index_121_; lean_object* v_size_122_; lean_object* v_keyArray_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_index_121_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_index_121_);
lean_dec_ref_known(v___x_117_, 1);
v_size_122_ = lean_ctor_get(v_m_80_, 0);
v_keyArray_123_ = lean_ctor_get(v_m_80_, 1);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_size_122_, v___x_124_);
v___x_126_ = lean_array_get_size(v_keyArray_123_);
v___x_127_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v___x_125_);
lean_dec(v_index_121_);
goto v___jp_90_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_mul(v___x_125_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = lean_nat_mul(v___x_126_, v___x_130_);
v___x_132_ = lean_nat_dec_le(v___x_129_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_129_);
if (v___x_132_ == 0)
{
lean_dec(v___x_125_);
lean_dec(v_index_121_);
goto v___jp_90_;
}
else
{
lean_object* v___x_133_; 
lean_dec_ref(v_inst_79_);
lean_dec_ref(v_inst_78_);
v___x_133_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_80_, v___x_125_, v_index_121_, v_a_81_, v_b_82_);
lean_dec(v_index_121_);
return v___x_133_;
}
}
}
default: 
{
lean_object* v_size_134_; lean_object* v_keyArray_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_size_134_ = lean_ctor_get(v_m_80_, 0);
v_keyArray_135_ = lean_ctor_get(v_m_80_, 1);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_size_134_, v___x_136_);
v___x_138_ = lean_array_get_size(v_keyArray_135_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec(v___x_137_);
lean_inc_ref(v_inst_79_);
lean_inc_ref(v_inst_78_);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_78_, v_inst_79_, v_m_80_);
v___y_108_ = v___x_140_;
goto v___jp_107_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_mul(v___x_137_, v___x_141_);
lean_dec(v___x_137_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_mul(v___x_138_, v___x_143_);
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v___x_142_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_inc_ref(v_inst_79_);
lean_inc_ref(v_inst_78_);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_78_, v_inst_79_, v_m_80_);
v___y_108_ = v___x_146_;
goto v___jp_107_;
}
else
{
v___y_108_ = v_m_80_;
goto v___jp_107_;
}
}
}
}
v___jp_83_:
{
lean_object* v_size_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_size_86_ = lean_ctor_get(v___y_84_, 0);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_size_86_, v___x_87_);
v___x_89_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_84_, v___x_88_, v_i_85_, v_a_81_, v_b_82_);
lean_dec(v_i_85_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_inc_ref(v_inst_79_);
lean_inc_ref(v_inst_78_);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_78_, v_inst_79_, v_m_80_);
lean_inc(v_a_81_);
v___x_92_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_78_, v_inst_79_, v___x_91_, v_a_81_);
switch(lean_obj_tag(v___x_92_))
{
case 0:
{
lean_object* v_index_93_; lean_object* v_size_94_; lean_object* v___x_95_; 
v_index_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_index_93_);
lean_dec_ref_known(v___x_92_, 3);
v_size_94_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_size_94_);
v___x_95_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_91_, v_size_94_, v_index_93_, v_a_81_, v_b_82_);
lean_dec(v_index_93_);
return v___x_95_;
}
case 1:
{
lean_object* v_index_96_; 
v_index_96_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_index_96_);
lean_dec_ref_known(v___x_92_, 1);
v___y_84_ = v___x_91_;
v_i_85_ = v_index_96_;
goto v___jp_83_;
}
default: 
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_91_, v___x_97_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_index_99_; 
v_index_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_index_99_);
lean_dec_ref_known(v___x_98_, 1);
v___y_84_ = v___x_91_;
v_i_85_ = v_index_99_;
goto v___jp_83_;
}
else
{
lean_dec(v_b_82_);
lean_dec(v_a_81_);
return v___x_91_;
}
}
}
}
v___jp_100_:
{
lean_object* v_size_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_size_103_ = lean_ctor_get(v___y_101_, 0);
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_size_103_, v___x_104_);
v___x_106_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_101_, v___x_105_, v_i_102_, v_a_81_, v_b_82_);
lean_dec(v_i_102_);
return v___x_106_;
}
v___jp_107_:
{
lean_object* v___x_109_; 
lean_inc(v_a_81_);
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_78_, v_inst_79_, v___y_108_, v_a_81_);
switch(lean_obj_tag(v___x_109_))
{
case 0:
{
lean_object* v_index_110_; lean_object* v_size_111_; lean_object* v___x_112_; 
v_index_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_index_110_);
lean_dec_ref_known(v___x_109_, 3);
v_size_111_ = lean_ctor_get(v___y_108_, 0);
lean_inc(v_size_111_);
v___x_112_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_108_, v_size_111_, v_index_110_, v_a_81_, v_b_82_);
lean_dec(v_index_110_);
return v___x_112_;
}
case 1:
{
lean_object* v_index_113_; 
v_index_113_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_index_113_);
lean_dec_ref_known(v___x_109_, 1);
v___y_101_ = v___y_108_;
v_i_102_ = v_index_113_;
goto v___jp_100_;
}
default: 
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_108_, v___x_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_index_116_; 
v_index_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_index_116_);
lean_dec_ref_known(v___x_115_, 1);
v___y_101_ = v___y_108_;
v_i_102_ = v_index_116_;
goto v___jp_100_;
}
else
{
lean_dec(v_b_82_);
lean_dec(v_a_81_);
return v___y_108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_m_151_, lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_149_, v_inst_150_, v_m_151_, v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_m_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_155_, v_inst_156_, v_m_157_, v_a_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_160_, v_inst_161_, v_m_162_, v_a_163_);
lean_dec_ref(v_m_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_167_, v_inst_169_, v_m_170_, v_a_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_m_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(v_00_u03b1_173_, v_00_u03b2_174_, v_inst_175_, v_inst_176_, v_inst_177_, v_m_178_, v_a_179_);
lean_dec_ref(v_m_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_m_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_181_, v_inst_182_, v_m_183_, v_a_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_186_, v_inst_187_, v_m_188_, v_a_189_);
lean_dec_ref(v_m_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_m_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_193_, v_inst_194_, v_m_195_, v_a_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_m_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(v_00_u03b1_198_, v_00_u03b2_199_, v_inst_200_, v_inst_201_, v_m_202_, v_a_203_);
lean_dec_ref(v_m_202_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_m_207_, lean_object* v_a_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_205_, v_inst_206_, v_m_207_, v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_m_212_, lean_object* v_a_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_210_, v_inst_211_, v_m_212_, v_a_213_);
lean_dec_ref(v_m_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_m_220_, lean_object* v_a_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_218_, v_inst_219_, v_m_220_, v_a_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___boxed(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_m_227_, lean_object* v_a_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(v_00_u03b1_223_, v_00_u03b2_224_, v_inst_225_, v_inst_226_, v_m_227_, v_a_228_);
lean_dec_ref(v_m_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_m_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; lean_object* v_val_236_; 
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_231_, v_inst_232_, v_m_233_, v_a_234_);
v_val_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_236_);
lean_dec(v___x_235_);
return v_val_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_m_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(v_inst_237_, v_inst_238_, v_m_239_, v_a_240_);
lean_dec_ref(v_m_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_m_247_, lean_object* v_a_248_, lean_object* v_h_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(v_inst_244_, v_inst_246_, v_m_247_, v_a_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_m_256_, lean_object* v_a_257_, lean_object* v_h_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098(v_00_u03b1_251_, v_00_u03b2_252_, v_inst_253_, v_inst_254_, v_inst_255_, v_m_256_, v_a_257_, v_h_258_);
lean_dec_ref(v_m_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_m_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_260_, v_inst_261_, v_m_262_, v_a_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(v_inst_265_, v_inst_266_, v_m_267_, v_a_268_);
lean_dec_ref(v_m_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_m_274_, lean_object* v_a_275_, lean_object* v_h_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_272_, v_inst_273_, v_m_274_, v_a_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_m_282_, lean_object* v_a_283_, lean_object* v_h_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(v_00_u03b1_278_, v_00_u03b2_279_, v_inst_280_, v_inst_281_, v_m_282_, v_a_283_, v_h_284_);
lean_dec_ref(v_m_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_m_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_286_, v_inst_287_, v_m_288_, v_a_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_291_, v_inst_292_, v_m_293_, v_a_294_);
lean_dec_ref(v_m_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(lean_object* v_00_u03b1_296_, lean_object* v_00_u03b2_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_m_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_298_, v_inst_299_, v_m_300_, v_a_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_303_, lean_object* v_00_u03b2_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_m_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(v_00_u03b1_303_, v_00_u03b2_304_, v_inst_305_, v_inst_306_, v_m_307_, v_a_308_);
lean_dec_ref(v_m_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_m_312_, lean_object* v_a_313_, lean_object* v_fallback_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_310_, v_inst_311_, v_m_312_, v_a_313_, v_fallback_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg___boxed(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_m_318_, lean_object* v_a_319_, lean_object* v_fallback_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(v_inst_316_, v_inst_317_, v_m_318_, v_a_319_, v_fallback_320_);
lean_dec_ref(v_fallback_320_);
lean_dec_ref(v_m_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_m_326_, lean_object* v_a_327_, lean_object* v_fallback_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_324_, v_inst_325_, v_m_326_, v_a_327_, v_fallback_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___boxed(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_m_334_, lean_object* v_a_335_, lean_object* v_fallback_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(v_00_u03b1_330_, v_00_u03b2_331_, v_inst_332_, v_inst_333_, v_m_334_, v_a_335_, v_fallback_336_);
lean_dec_ref(v_fallback_336_);
lean_dec_ref(v_m_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_338_, v_inst_339_, v_m_341_, v_a_342_, v_inst_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_m_347_, v_a_348_);
lean_dec_ref(v_m_347_);
lean_dec_ref(v_inst_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_m_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_352_, v_inst_353_, v_m_355_, v_a_356_, v_inst_354_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_m_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(v_00_u03b1_358_, v_00_u03b2_359_, v_inst_360_, v_inst_361_, v_inst_362_, v_m_363_, v_a_364_);
lean_dec_ref(v_m_363_);
lean_dec_ref(v_inst_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_m_368_, lean_object* v_a_369_, lean_object* v_fallback_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_366_, v_inst_367_, v_m_368_, v_a_369_, v_fallback_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_m_374_, lean_object* v_a_375_, lean_object* v_fallback_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(v_inst_372_, v_inst_373_, v_m_374_, v_a_375_, v_fallback_376_);
lean_dec(v_fallback_376_);
lean_dec_ref(v_m_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_m_383_, lean_object* v_a_384_, lean_object* v_fallback_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_380_, v_inst_382_, v_m_383_, v_a_384_, v_fallback_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___boxed(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_m_392_, lean_object* v_a_393_, lean_object* v_fallback_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(v_00_u03b1_387_, v_00_u03b2_388_, v_inst_389_, v_inst_390_, v_inst_391_, v_m_392_, v_a_393_, v_fallback_394_);
lean_dec(v_fallback_394_);
lean_dec_ref(v_m_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_m_398_, lean_object* v_a_399_, lean_object* v_inst_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_396_, v_inst_397_, v_m_398_, v_a_399_, v_inst_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_m_404_, lean_object* v_a_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(v_inst_402_, v_inst_403_, v_m_404_, v_a_405_, v_inst_406_);
lean_dec(v_inst_406_);
lean_dec_ref(v_m_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_m_413_, lean_object* v_a_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_410_, v_inst_412_, v_m_413_, v_a_414_, v_inst_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___boxed(lean_object* v_00_u03b1_417_, lean_object* v_00_u03b2_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_inst_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(v_00_u03b1_417_, v_00_u03b2_418_, v_inst_419_, v_inst_420_, v_inst_421_, v_m_422_, v_a_423_, v_inst_424_);
lean_dec(v_inst_424_);
lean_dec_ref(v_m_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; lean_object* v_val_431_; 
v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_426_, v_inst_427_, v_m_428_, v_a_429_);
v_val_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_431_);
lean_dec(v___x_430_);
return v_val_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_m_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(v_inst_432_, v_inst_433_, v_m_434_, v_a_435_);
lean_dec_ref(v_m_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_m_441_, lean_object* v_a_442_, lean_object* v_h_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(v_inst_439_, v_inst_440_, v_m_441_, v_a_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(lean_object* v_00_u03b1_445_, lean_object* v_00_u03b2_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_m_449_, lean_object* v_a_450_, lean_object* v_h_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(v_00_u03b1_445_, v_00_u03b2_446_, v_inst_447_, v_inst_448_, v_m_449_, v_a_450_, v_h_451_);
lean_dec_ref(v_m_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_fallback_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_453_, v_inst_454_, v_m_455_, v_a_456_, v_fallback_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_m_461_, lean_object* v_a_462_, lean_object* v_fallback_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(v_inst_459_, v_inst_460_, v_m_461_, v_a_462_, v_fallback_463_);
lean_dec(v_fallback_463_);
lean_dec_ref(v_m_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_m_469_, lean_object* v_a_470_, lean_object* v_fallback_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_467_, v_inst_468_, v_m_469_, v_a_470_, v_fallback_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___boxed(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_m_477_, lean_object* v_a_478_, lean_object* v_fallback_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(v_00_u03b1_473_, v_00_u03b2_474_, v_inst_475_, v_inst_476_, v_m_477_, v_a_478_, v_fallback_479_);
lean_dec(v_fallback_479_);
lean_dec_ref(v_m_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_481_, v_inst_482_, v_inst_483_, v_m_484_, v_a_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_m_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(v_inst_487_, v_inst_488_, v_inst_489_, v_m_490_, v_a_491_);
lean_dec_ref(v_m_490_);
lean_dec(v_inst_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_m_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_495_, v_inst_496_, v_inst_497_, v_m_498_, v_a_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(v_00_u03b1_501_, v_00_u03b2_502_, v_inst_503_, v_inst_504_, v_inst_505_, v_m_506_, v_a_507_);
lean_dec_ref(v_m_506_);
lean_dec(v_inst_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_m_511_, lean_object* v_a_512_, lean_object* v_b_513_){
_start:
{
lean_object* v___y_515_; lean_object* v_i_516_; lean_object* v___y_532_; lean_object* v_i_533_; lean_object* v___y_539_; lean_object* v___x_548_; 
lean_inc(v_a_512_);
lean_inc_ref(v_inst_510_);
lean_inc_ref(v_inst_509_);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_509_, v_inst_510_, v_m_511_, v_a_512_);
switch(lean_obj_tag(v___x_548_))
{
case 0:
{
lean_object* v_index_549_; lean_object* v_size_550_; lean_object* v___x_551_; 
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_inst_509_);
v_index_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_548_, 3);
v_size_550_ = lean_ctor_get(v_m_511_, 0);
lean_inc(v_size_550_);
v___x_551_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_511_, v_size_550_, v_index_549_, v_a_512_, v_b_513_);
lean_dec(v_index_549_);
return v___x_551_;
}
case 1:
{
lean_object* v_index_552_; lean_object* v_size_553_; lean_object* v_keyArray_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_index_552_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_552_);
lean_dec_ref_known(v___x_548_, 1);
v_size_553_ = lean_ctor_get(v_m_511_, 0);
v_keyArray_554_ = lean_ctor_get(v_m_511_, 1);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_size_553_, v___x_555_);
v___x_557_ = lean_array_get_size(v_keyArray_554_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v___x_556_);
lean_dec(v_index_552_);
goto v___jp_521_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_nat_mul(v___x_556_, v___x_559_);
v___x_561_ = lean_unsigned_to_nat(3u);
v___x_562_ = lean_nat_mul(v___x_557_, v___x_561_);
v___x_563_ = lean_nat_dec_le(v___x_560_, v___x_562_);
lean_dec(v___x_562_);
lean_dec(v___x_560_);
if (v___x_563_ == 0)
{
lean_dec(v___x_556_);
lean_dec(v_index_552_);
goto v___jp_521_;
}
else
{
lean_object* v___x_564_; 
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_inst_509_);
v___x_564_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_511_, v___x_556_, v_index_552_, v_a_512_, v_b_513_);
lean_dec(v_index_552_);
return v___x_564_;
}
}
}
default: 
{
lean_object* v_size_565_; lean_object* v_keyArray_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_size_565_ = lean_ctor_get(v_m_511_, 0);
v_keyArray_566_ = lean_ctor_get(v_m_511_, 1);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_size_565_, v___x_567_);
v___x_569_ = lean_array_get_size(v_keyArray_566_);
v___x_570_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v___x_568_);
lean_inc_ref(v_inst_510_);
lean_inc_ref(v_inst_509_);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_509_, v_inst_510_, v_m_511_);
v___y_539_ = v___x_571_;
goto v___jp_538_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_572_ = lean_unsigned_to_nat(4u);
v___x_573_ = lean_nat_mul(v___x_568_, v___x_572_);
lean_dec(v___x_568_);
v___x_574_ = lean_unsigned_to_nat(3u);
v___x_575_ = lean_nat_mul(v___x_569_, v___x_574_);
v___x_576_ = lean_nat_dec_le(v___x_573_, v___x_575_);
lean_dec(v___x_575_);
lean_dec(v___x_573_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_inc_ref(v_inst_510_);
lean_inc_ref(v_inst_509_);
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_509_, v_inst_510_, v_m_511_);
v___y_539_ = v___x_577_;
goto v___jp_538_;
}
else
{
v___y_539_ = v_m_511_;
goto v___jp_538_;
}
}
}
}
v___jp_514_:
{
lean_object* v_size_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_size_517_ = lean_ctor_get(v___y_515_, 0);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_size_517_, v___x_518_);
v___x_520_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_515_, v___x_519_, v_i_516_, v_a_512_, v_b_513_);
lean_dec(v_i_516_);
return v___x_520_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc_ref(v_inst_510_);
lean_inc_ref(v_inst_509_);
v___x_522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_509_, v_inst_510_, v_m_511_);
lean_inc(v_a_512_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_509_, v_inst_510_, v___x_522_, v_a_512_);
switch(lean_obj_tag(v___x_523_))
{
case 0:
{
lean_object* v_index_524_; lean_object* v_size_525_; lean_object* v___x_526_; 
v_index_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_index_524_);
lean_dec_ref_known(v___x_523_, 3);
v_size_525_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_size_525_);
v___x_526_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_522_, v_size_525_, v_index_524_, v_a_512_, v_b_513_);
lean_dec(v_index_524_);
return v___x_526_;
}
case 1:
{
lean_object* v_index_527_; 
v_index_527_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_index_527_);
lean_dec_ref_known(v___x_523_, 1);
v___y_515_ = v___x_522_;
v_i_516_ = v_index_527_;
goto v___jp_514_;
}
default: 
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_522_, v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_index_530_; 
v_index_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_index_530_);
lean_dec_ref_known(v___x_529_, 1);
v___y_515_ = v___x_522_;
v_i_516_ = v_index_530_;
goto v___jp_514_;
}
else
{
lean_dec(v_b_513_);
lean_dec(v_a_512_);
return v___x_522_;
}
}
}
}
v___jp_531_:
{
lean_object* v_size_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_size_534_ = lean_ctor_get(v___y_532_, 0);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_534_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_532_, v___x_536_, v_i_533_, v_a_512_, v_b_513_);
lean_dec(v_i_533_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_540_; 
lean_inc(v_a_512_);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_509_, v_inst_510_, v___y_539_, v_a_512_);
switch(lean_obj_tag(v___x_540_))
{
case 0:
{
lean_object* v_index_541_; lean_object* v_size_542_; lean_object* v___x_543_; 
v_index_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_index_541_);
lean_dec_ref_known(v___x_540_, 3);
v_size_542_ = lean_ctor_get(v___y_539_, 0);
lean_inc(v_size_542_);
v___x_543_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_539_, v_size_542_, v_index_541_, v_a_512_, v_b_513_);
lean_dec(v_index_541_);
return v___x_543_;
}
case 1:
{
lean_object* v_index_544_; 
v_index_544_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_index_544_);
lean_dec_ref_known(v___x_540_, 1);
v___y_532_ = v___y_539_;
v_i_533_ = v_index_544_;
goto v___jp_531_;
}
default: 
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_539_, v___x_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_index_547_; 
v_index_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_index_547_);
lean_dec_ref_known(v___x_546_, 1);
v___y_532_ = v___y_539_;
v_i_533_ = v_index_547_;
goto v___jp_531_;
}
else
{
lean_dec(v_b_513_);
lean_dec(v_a_512_);
return v___y_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_m_582_, lean_object* v_a_583_, lean_object* v_b_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(v_inst_580_, v_inst_581_, v_m_582_, v_a_583_, v_b_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_m_588_, lean_object* v_a_589_, lean_object* v_b_590_){
_start:
{
lean_object* v___y_592_; lean_object* v_i_593_; lean_object* v___y_609_; lean_object* v_i_610_; lean_object* v___y_616_; lean_object* v___x_625_; 
lean_inc(v_a_589_);
lean_inc_ref(v_inst_587_);
lean_inc_ref(v_inst_586_);
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_586_, v_inst_587_, v_m_588_, v_a_589_);
switch(lean_obj_tag(v___x_625_))
{
case 0:
{
lean_dec_ref_known(v___x_625_, 3);
lean_dec(v_b_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_inst_587_);
lean_dec_ref(v_inst_586_);
return v_m_588_;
}
case 1:
{
lean_object* v_index_626_; lean_object* v_size_627_; lean_object* v_keyArray_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_index_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_index_626_);
lean_dec_ref_known(v___x_625_, 1);
v_size_627_ = lean_ctor_get(v_m_588_, 0);
v_keyArray_628_ = lean_ctor_get(v_m_588_, 1);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_size_627_, v___x_629_);
v___x_631_ = lean_array_get_size(v_keyArray_628_);
v___x_632_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec(v___x_630_);
lean_dec(v_index_626_);
goto v___jp_598_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_633_ = lean_unsigned_to_nat(4u);
v___x_634_ = lean_nat_mul(v___x_630_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(3u);
v___x_636_ = lean_nat_mul(v___x_631_, v___x_635_);
v___x_637_ = lean_nat_dec_le(v___x_634_, v___x_636_);
lean_dec(v___x_636_);
lean_dec(v___x_634_);
if (v___x_637_ == 0)
{
lean_dec(v___x_630_);
lean_dec(v_index_626_);
goto v___jp_598_;
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v_inst_587_);
lean_dec_ref(v_inst_586_);
v___x_638_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_588_, v___x_630_, v_index_626_, v_a_589_, v_b_590_);
lean_dec(v_index_626_);
return v___x_638_;
}
}
}
default: 
{
lean_object* v_size_639_; lean_object* v_keyArray_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_size_639_ = lean_ctor_get(v_m_588_, 0);
v_keyArray_640_ = lean_ctor_get(v_m_588_, 1);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_size_639_, v___x_641_);
v___x_643_ = lean_array_get_size(v_keyArray_640_);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v___x_642_);
lean_inc_ref(v_inst_587_);
lean_inc_ref(v_inst_586_);
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_586_, v_inst_587_, v_m_588_);
v___y_616_ = v___x_645_;
goto v___jp_615_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_646_ = lean_unsigned_to_nat(4u);
v___x_647_ = lean_nat_mul(v___x_642_, v___x_646_);
lean_dec(v___x_642_);
v___x_648_ = lean_unsigned_to_nat(3u);
v___x_649_ = lean_nat_mul(v___x_643_, v___x_648_);
v___x_650_ = lean_nat_dec_le(v___x_647_, v___x_649_);
lean_dec(v___x_649_);
lean_dec(v___x_647_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_inc_ref(v_inst_587_);
lean_inc_ref(v_inst_586_);
v___x_651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_586_, v_inst_587_, v_m_588_);
v___y_616_ = v___x_651_;
goto v___jp_615_;
}
else
{
v___y_616_ = v_m_588_;
goto v___jp_615_;
}
}
}
}
v___jp_591_:
{
lean_object* v_size_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_size_594_ = lean_ctor_get(v___y_592_, 0);
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_size_594_, v___x_595_);
v___x_597_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_592_, v___x_596_, v_i_593_, v_a_589_, v_b_590_);
lean_dec(v_i_593_);
return v___x_597_;
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_inc_ref(v_inst_587_);
lean_inc_ref(v_inst_586_);
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_586_, v_inst_587_, v_m_588_);
lean_inc(v_a_589_);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_586_, v_inst_587_, v___x_599_, v_a_589_);
switch(lean_obj_tag(v___x_600_))
{
case 0:
{
lean_object* v_index_601_; lean_object* v_size_602_; lean_object* v___x_603_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 3);
v_size_602_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_size_602_);
v___x_603_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_599_, v_size_602_, v_index_601_, v_a_589_, v_b_590_);
lean_dec(v_index_601_);
return v___x_603_;
}
case 1:
{
lean_object* v_index_604_; 
v_index_604_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_604_);
lean_dec_ref_known(v___x_600_, 1);
v___y_592_ = v___x_599_;
v_i_593_ = v_index_604_;
goto v___jp_591_;
}
default: 
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_599_, v___x_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_index_607_; 
v_index_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_index_607_);
lean_dec_ref_known(v___x_606_, 1);
v___y_592_ = v___x_599_;
v_i_593_ = v_index_607_;
goto v___jp_591_;
}
else
{
lean_dec(v_b_590_);
lean_dec(v_a_589_);
return v___x_599_;
}
}
}
}
v___jp_608_:
{
lean_object* v_size_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_size_611_ = lean_ctor_get(v___y_609_, 0);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_size_611_, v___x_612_);
v___x_614_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_609_, v___x_613_, v_i_610_, v_a_589_, v_b_590_);
lean_dec(v_i_610_);
return v___x_614_;
}
v___jp_615_:
{
lean_object* v___x_617_; 
lean_inc(v_a_589_);
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_586_, v_inst_587_, v___y_616_, v_a_589_);
switch(lean_obj_tag(v___x_617_))
{
case 0:
{
lean_object* v_index_618_; lean_object* v_size_619_; lean_object* v___x_620_; 
v_index_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_618_);
lean_dec_ref_known(v___x_617_, 3);
v_size_619_ = lean_ctor_get(v___y_616_, 0);
lean_inc(v_size_619_);
v___x_620_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_616_, v_size_619_, v_index_618_, v_a_589_, v_b_590_);
lean_dec(v_index_618_);
return v___x_620_;
}
case 1:
{
lean_object* v_index_621_; 
v_index_621_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_621_);
lean_dec_ref_known(v___x_617_, 1);
v___y_609_ = v___y_616_;
v_i_610_ = v_index_621_;
goto v___jp_608_;
}
default: 
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_616_, v___x_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_index_624_; 
v_index_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_index_624_);
lean_dec_ref_known(v___x_623_, 1);
v___y_609_ = v___y_616_;
v_i_610_ = v_index_624_;
goto v___jp_608_;
}
else
{
lean_dec(v_b_590_);
lean_dec(v_a_589_);
return v___y_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_m_656_, lean_object* v_a_657_, lean_object* v_b_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(v_inst_654_, v_inst_655_, v_m_656_, v_a_657_, v_b_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_m_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_660_, v_inst_661_, v_m_662_, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_m_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_667_, v_inst_668_, v_m_669_, v_a_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_m_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_672_, v_inst_673_, v_m_674_, v_a_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_m_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_679_, v_inst_680_, v_m_681_, v_a_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_m_686_, lean_object* v_a_687_, lean_object* v_f_688_){
_start:
{
lean_object* v___x_689_; 
lean_inc(v_a_687_);
lean_inc_ref(v_inst_685_);
lean_inc_ref(v_inst_684_);
v___x_689_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_684_, v_inst_685_, v_m_686_, v_a_687_);
switch(lean_obj_tag(v___x_689_))
{
case 0:
{
lean_object* v_index_690_; lean_object* v_value_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_inst_685_);
lean_dec_ref(v_inst_684_);
v_index_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_index_690_);
v_value_691_ = lean_ctor_get(v___x_689_, 2);
lean_inc(v_value_691_);
lean_dec_ref_known(v___x_689_, 3);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v_value_691_);
v___x_693_ = lean_apply_1(v_f_688_, v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_size_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_a_687_);
v_size_694_ = lean_ctor_get(v_m_686_, 0);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_sub(v_size_694_, v___x_695_);
v___x_697_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_686_, v___x_696_, v_index_690_);
lean_dec(v_index_690_);
return v___x_697_;
}
else
{
lean_object* v_val_698_; lean_object* v_size_699_; lean_object* v___x_700_; 
v_val_698_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v___x_693_, 1);
v_size_699_ = lean_ctor_get(v_m_686_, 0);
lean_inc(v_size_699_);
v___x_700_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_686_, v_size_699_, v_index_690_, v_a_687_, v_val_698_);
lean_dec(v_index_690_);
return v___x_700_;
}
}
case 1:
{
lean_object* v_index_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_index_701_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_index_701_);
lean_dec_ref_known(v___x_689_, 1);
v___x_702_ = lean_box(0);
v___x_703_ = lean_apply_1(v_f_688_, v___x_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_dec(v_index_701_);
lean_dec(v_a_687_);
lean_dec_ref(v_inst_685_);
lean_dec_ref(v_inst_684_);
return v_m_686_;
}
else
{
lean_object* v_val_704_; lean_object* v___y_706_; lean_object* v_i_707_; lean_object* v_size_722_; lean_object* v_keyArray_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_val_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v___x_703_, 1);
v_size_722_ = lean_ctor_get(v_m_686_, 0);
v_keyArray_723_ = lean_ctor_get(v_m_686_, 1);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_size_722_, v___x_724_);
v___x_726_ = lean_array_get_size(v_keyArray_723_);
v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_index_701_);
goto v___jp_712_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_728_ = lean_unsigned_to_nat(4u);
v___x_729_ = lean_nat_mul(v___x_725_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(3u);
v___x_731_ = lean_nat_mul(v___x_726_, v___x_730_);
v___x_732_ = lean_nat_dec_le(v___x_729_, v___x_731_);
lean_dec(v___x_731_);
lean_dec(v___x_729_);
if (v___x_732_ == 0)
{
lean_dec(v___x_725_);
lean_dec(v_index_701_);
goto v___jp_712_;
}
else
{
lean_object* v___x_733_; 
lean_dec_ref(v_inst_685_);
lean_dec_ref(v_inst_684_);
v___x_733_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_686_, v___x_725_, v_index_701_, v_a_687_, v_val_704_);
lean_dec(v_index_701_);
return v___x_733_;
}
}
v___jp_705_:
{
lean_object* v_size_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_size_708_ = lean_ctor_get(v___y_706_, 0);
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = lean_nat_add(v_size_708_, v___x_709_);
v___x_711_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_706_, v___x_710_, v_i_707_, v_a_687_, v_val_704_);
lean_dec(v_i_707_);
return v___x_711_;
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc_ref(v_inst_685_);
lean_inc_ref(v_inst_684_);
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_684_, v_inst_685_, v_m_686_);
lean_inc(v_a_687_);
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_684_, v_inst_685_, v___x_713_, v_a_687_);
switch(lean_obj_tag(v___x_714_))
{
case 0:
{
lean_object* v_index_715_; lean_object* v_size_716_; lean_object* v___x_717_; 
v_index_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_index_715_);
lean_dec_ref_known(v___x_714_, 3);
v_size_716_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_size_716_);
v___x_717_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_713_, v_size_716_, v_index_715_, v_a_687_, v_val_704_);
lean_dec(v_index_715_);
return v___x_717_;
}
case 1:
{
lean_object* v_index_718_; 
v_index_718_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_index_718_);
lean_dec_ref_known(v___x_714_, 1);
v___y_706_ = v___x_713_;
v_i_707_ = v_index_718_;
goto v___jp_705_;
}
default: 
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_713_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_index_721_; 
v_index_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_index_721_);
lean_dec_ref_known(v___x_720_, 1);
v___y_706_ = v___x_713_;
v_i_707_ = v_index_721_;
goto v___jp_705_;
}
else
{
lean_dec(v_val_704_);
lean_dec(v_a_687_);
return v___x_713_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = lean_apply_1(v_f_688_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_dec(v_a_687_);
lean_dec_ref(v_inst_685_);
lean_dec_ref(v_inst_684_);
return v_m_686_;
}
else
{
lean_object* v_val_736_; lean_object* v___y_738_; lean_object* v_i_739_; lean_object* v___y_745_; lean_object* v_size_754_; lean_object* v_keyArray_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
v_size_754_ = lean_ctor_get(v_m_686_, 0);
v_keyArray_755_ = lean_ctor_get(v_m_686_, 1);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_size_754_, v___x_756_);
v___x_758_ = lean_array_get_size(v_keyArray_755_);
v___x_759_ = lean_nat_dec_lt(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec(v___x_757_);
lean_inc_ref(v_inst_685_);
lean_inc_ref(v_inst_684_);
v___x_760_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_684_, v_inst_685_, v_m_686_);
v___y_745_ = v___x_760_;
goto v___jp_744_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = lean_nat_mul(v___x_757_, v___x_761_);
lean_dec(v___x_757_);
v___x_763_ = lean_unsigned_to_nat(3u);
v___x_764_ = lean_nat_mul(v___x_758_, v___x_763_);
v___x_765_ = lean_nat_dec_le(v___x_762_, v___x_764_);
lean_dec(v___x_764_);
lean_dec(v___x_762_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_inc_ref(v_inst_685_);
lean_inc_ref(v_inst_684_);
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_684_, v_inst_685_, v_m_686_);
v___y_745_ = v___x_766_;
goto v___jp_744_;
}
else
{
v___y_745_ = v_m_686_;
goto v___jp_744_;
}
}
v___jp_737_:
{
lean_object* v_size_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_size_740_ = lean_ctor_get(v___y_738_, 0);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v_size_740_, v___x_741_);
v___x_743_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_738_, v___x_742_, v_i_739_, v_a_687_, v_val_736_);
lean_dec(v_i_739_);
return v___x_743_;
}
v___jp_744_:
{
lean_object* v___x_746_; 
lean_inc(v_a_687_);
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_684_, v_inst_685_, v___y_745_, v_a_687_);
switch(lean_obj_tag(v___x_746_))
{
case 0:
{
lean_object* v_index_747_; lean_object* v_size_748_; lean_object* v___x_749_; 
v_index_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_index_747_);
lean_dec_ref_known(v___x_746_, 3);
v_size_748_ = lean_ctor_get(v___y_745_, 0);
lean_inc(v_size_748_);
v___x_749_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_745_, v_size_748_, v_index_747_, v_a_687_, v_val_736_);
lean_dec(v_index_747_);
return v___x_749_;
}
case 1:
{
lean_object* v_index_750_; 
v_index_750_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_index_750_);
lean_dec_ref_known(v___x_746_, 1);
v___y_738_ = v___y_745_;
v_i_739_ = v_index_750_;
goto v___jp_737_;
}
default: 
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_745_, v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_index_753_; 
v_index_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_753_);
lean_dec_ref_known(v___x_752_, 1);
v___y_738_ = v___y_745_;
v_i_739_ = v_index_753_;
goto v___jp_737_;
}
else
{
lean_dec(v_val_736_);
lean_dec(v_a_687_);
return v___y_745_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_m_772_, lean_object* v_a_773_, lean_object* v_f_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(v_inst_769_, v_inst_770_, v_m_772_, v_a_773_, v_f_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_m_778_, lean_object* v_a_779_, lean_object* v_f_780_){
_start:
{
lean_object* v___x_781_; 
lean_inc(v_a_779_);
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_776_, v_inst_777_, v_m_778_, v_a_779_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_index_782_; lean_object* v_value_783_; lean_object* v_size_784_; lean_object* v_v_x27_785_; lean_object* v___x_786_; 
v_index_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_index_782_);
v_value_783_ = lean_ctor_get(v___x_781_, 2);
lean_inc(v_value_783_);
lean_dec_ref_known(v___x_781_, 3);
v_size_784_ = lean_ctor_get(v_m_778_, 0);
lean_inc(v_size_784_);
v_v_x27_785_ = lean_apply_1(v_f_780_, v_value_783_);
v___x_786_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_778_, v_size_784_, v_index_782_, v_a_779_, v_v_x27_785_);
lean_dec(v_index_782_);
return v___x_786_;
}
else
{
lean_dec(v___x_781_);
lean_dec(v_f_780_);
lean_dec(v_a_779_);
return v_m_778_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_m_792_, lean_object* v_a_793_, lean_object* v_f_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(v_inst_789_, v_inst_790_, v_m_792_, v_a_793_, v_f_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_f_800_){
_start:
{
lean_object* v___x_801_; 
lean_inc(v_a_799_);
lean_inc_ref(v_inst_797_);
lean_inc_ref(v_inst_796_);
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_796_, v_inst_797_, v_m_798_, v_a_799_);
switch(lean_obj_tag(v___x_801_))
{
case 0:
{
lean_object* v_index_802_; lean_object* v_value_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v_inst_797_);
lean_dec_ref(v_inst_796_);
v_index_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_index_802_);
v_value_803_ = lean_ctor_get(v___x_801_, 2);
lean_inc(v_value_803_);
lean_dec_ref_known(v___x_801_, 3);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_value_803_);
v___x_805_ = lean_apply_1(v_f_800_, v___x_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_size_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_a_799_);
v_size_806_ = lean_ctor_get(v_m_798_, 0);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_sub(v_size_806_, v___x_807_);
v___x_809_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_798_, v___x_808_, v_index_802_);
lean_dec(v_index_802_);
return v___x_809_;
}
else
{
lean_object* v_val_810_; lean_object* v_size_811_; lean_object* v___x_812_; 
v_val_810_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v___x_805_, 1);
v_size_811_ = lean_ctor_get(v_m_798_, 0);
lean_inc(v_size_811_);
v___x_812_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_798_, v_size_811_, v_index_802_, v_a_799_, v_val_810_);
lean_dec(v_index_802_);
return v___x_812_;
}
}
case 1:
{
lean_object* v_index_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_index_813_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_index_813_);
lean_dec_ref_known(v___x_801_, 1);
v___x_814_ = lean_box(0);
v___x_815_ = lean_apply_1(v_f_800_, v___x_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec(v_index_813_);
lean_dec(v_a_799_);
lean_dec_ref(v_inst_797_);
lean_dec_ref(v_inst_796_);
return v_m_798_;
}
else
{
lean_object* v_val_816_; lean_object* v___y_818_; lean_object* v_i_819_; lean_object* v_size_834_; lean_object* v_keyArray_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_val_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_816_);
lean_dec_ref_known(v___x_815_, 1);
v_size_834_ = lean_ctor_get(v_m_798_, 0);
v_keyArray_835_ = lean_ctor_get(v_m_798_, 1);
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_size_834_, v___x_836_);
v___x_838_ = lean_array_get_size(v_keyArray_835_);
v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec(v___x_837_);
lean_dec(v_index_813_);
goto v___jp_824_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_840_ = lean_unsigned_to_nat(4u);
v___x_841_ = lean_nat_mul(v___x_837_, v___x_840_);
v___x_842_ = lean_unsigned_to_nat(3u);
v___x_843_ = lean_nat_mul(v___x_838_, v___x_842_);
v___x_844_ = lean_nat_dec_le(v___x_841_, v___x_843_);
lean_dec(v___x_843_);
lean_dec(v___x_841_);
if (v___x_844_ == 0)
{
lean_dec(v___x_837_);
lean_dec(v_index_813_);
goto v___jp_824_;
}
else
{
lean_object* v___x_845_; 
lean_dec_ref(v_inst_797_);
lean_dec_ref(v_inst_796_);
v___x_845_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_798_, v___x_837_, v_index_813_, v_a_799_, v_val_816_);
lean_dec(v_index_813_);
return v___x_845_;
}
}
v___jp_817_:
{
lean_object* v_size_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_size_820_ = lean_ctor_get(v___y_818_, 0);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_size_820_, v___x_821_);
v___x_823_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_818_, v___x_822_, v_i_819_, v_a_799_, v_val_816_);
lean_dec(v_i_819_);
return v___x_823_;
}
v___jp_824_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_inc_ref(v_inst_797_);
lean_inc_ref(v_inst_796_);
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_796_, v_inst_797_, v_m_798_);
lean_inc(v_a_799_);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_796_, v_inst_797_, v___x_825_, v_a_799_);
switch(lean_obj_tag(v___x_826_))
{
case 0:
{
lean_object* v_index_827_; lean_object* v_size_828_; lean_object* v___x_829_; 
v_index_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_827_);
lean_dec_ref_known(v___x_826_, 3);
v_size_828_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_size_828_);
v___x_829_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_825_, v_size_828_, v_index_827_, v_a_799_, v_val_816_);
lean_dec(v_index_827_);
return v___x_829_;
}
case 1:
{
lean_object* v_index_830_; 
v_index_830_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_830_);
lean_dec_ref_known(v___x_826_, 1);
v___y_818_ = v___x_825_;
v_i_819_ = v_index_830_;
goto v___jp_817_;
}
default: 
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_825_, v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_index_833_; 
v_index_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_index_833_);
lean_dec_ref_known(v___x_832_, 1);
v___y_818_ = v___x_825_;
v_i_819_ = v_index_833_;
goto v___jp_817_;
}
else
{
lean_dec(v_val_816_);
lean_dec(v_a_799_);
return v___x_825_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_box(0);
v___x_847_ = lean_apply_1(v_f_800_, v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_dec(v_a_799_);
lean_dec_ref(v_inst_797_);
lean_dec_ref(v_inst_796_);
return v_m_798_;
}
else
{
lean_object* v_val_848_; lean_object* v___y_850_; lean_object* v_i_851_; lean_object* v___y_857_; lean_object* v_size_866_; lean_object* v_keyArray_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_val_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v___x_847_, 1);
v_size_866_ = lean_ctor_get(v_m_798_, 0);
v_keyArray_867_ = lean_ctor_get(v_m_798_, 1);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_size_866_, v___x_868_);
v___x_870_ = lean_array_get_size(v_keyArray_867_);
v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec(v___x_869_);
lean_inc_ref(v_inst_797_);
lean_inc_ref(v_inst_796_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_796_, v_inst_797_, v_m_798_);
v___y_857_ = v___x_872_;
goto v___jp_856_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_873_ = lean_unsigned_to_nat(4u);
v___x_874_ = lean_nat_mul(v___x_869_, v___x_873_);
lean_dec(v___x_869_);
v___x_875_ = lean_unsigned_to_nat(3u);
v___x_876_ = lean_nat_mul(v___x_870_, v___x_875_);
v___x_877_ = lean_nat_dec_le(v___x_874_, v___x_876_);
lean_dec(v___x_876_);
lean_dec(v___x_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_inc_ref(v_inst_797_);
lean_inc_ref(v_inst_796_);
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_796_, v_inst_797_, v_m_798_);
v___y_857_ = v___x_878_;
goto v___jp_856_;
}
else
{
v___y_857_ = v_m_798_;
goto v___jp_856_;
}
}
v___jp_849_:
{
lean_object* v_size_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_size_852_ = lean_ctor_get(v___y_850_, 0);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_size_852_, v___x_853_);
v___x_855_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_850_, v___x_854_, v_i_851_, v_a_799_, v_val_848_);
lean_dec(v_i_851_);
return v___x_855_;
}
v___jp_856_:
{
lean_object* v___x_858_; 
lean_inc(v_a_799_);
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_796_, v_inst_797_, v___y_857_, v_a_799_);
switch(lean_obj_tag(v___x_858_))
{
case 0:
{
lean_object* v_index_859_; lean_object* v_size_860_; lean_object* v___x_861_; 
v_index_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_index_859_);
lean_dec_ref_known(v___x_858_, 3);
v_size_860_ = lean_ctor_get(v___y_857_, 0);
lean_inc(v_size_860_);
v___x_861_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_857_, v_size_860_, v_index_859_, v_a_799_, v_val_848_);
lean_dec(v_index_859_);
return v___x_861_;
}
case 1:
{
lean_object* v_index_862_; 
v_index_862_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_index_862_);
lean_dec_ref_known(v___x_858_, 1);
v___y_850_ = v___y_857_;
v_i_851_ = v_index_862_;
goto v___jp_849_;
}
default: 
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_857_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_index_865_; 
v_index_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_index_865_);
lean_dec_ref_known(v___x_864_, 1);
v___y_850_ = v___y_857_;
v_i_851_ = v_index_865_;
goto v___jp_849_;
}
else
{
lean_dec(v_val_848_);
lean_dec(v_a_799_);
return v___y_857_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_m_883_, lean_object* v_a_884_, lean_object* v_f_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(v_inst_881_, v_inst_882_, v_m_883_, v_a_884_, v_f_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_m_889_, lean_object* v_a_890_, lean_object* v_f_891_){
_start:
{
lean_object* v___x_892_; 
lean_inc(v_a_890_);
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_887_, v_inst_888_, v_m_889_, v_a_890_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_index_893_; lean_object* v_value_894_; lean_object* v_size_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_index_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_index_893_);
v_value_894_ = lean_ctor_get(v___x_892_, 2);
lean_inc(v_value_894_);
lean_dec_ref_known(v___x_892_, 3);
v_size_895_ = lean_ctor_get(v_m_889_, 0);
lean_inc(v_size_895_);
v___x_896_ = lean_apply_1(v_f_891_, v_value_894_);
v___x_897_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_889_, v_size_895_, v_index_893_, v_a_890_, v___x_896_);
lean_dec(v_index_893_);
return v___x_897_;
}
else
{
lean_dec(v___x_892_);
lean_dec(v_f_891_);
lean_dec(v_a_890_);
return v_m_889_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098(lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_m_902_, lean_object* v_a_903_, lean_object* v_f_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(v_inst_900_, v_inst_901_, v_m_902_, v_a_903_, v_f_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_m_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_906_, v_inst_907_, v_m_908_, v_a_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_911_, v_inst_912_, v_m_913_, v_a_914_);
lean_dec_ref(v_m_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_m_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_918_, v_inst_919_, v_m_920_, v_a_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_m_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(v_00_u03b1_923_, v_00_u03b2_924_, v_inst_925_, v_inst_926_, v_m_927_, v_a_928_);
lean_dec_ref(v_m_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_m_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_934_; lean_object* v_val_935_; 
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_930_, v_inst_931_, v_m_932_, v_a_933_);
v_val_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_935_);
lean_dec(v___x_934_);
return v_val_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_m_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_936_, v_inst_937_, v_m_938_, v_a_939_);
lean_dec_ref(v_m_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_m_945_, lean_object* v_a_946_, lean_object* v_h_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_943_, v_inst_944_, v_m_945_, v_a_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_m_953_, lean_object* v_a_954_, lean_object* v_h_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(v_00_u03b1_949_, v_00_u03b2_950_, v_inst_951_, v_inst_952_, v_m_953_, v_a_954_, v_h_955_);
lean_dec_ref(v_m_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_m_959_, lean_object* v_a_960_, lean_object* v_fallback_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_957_, v_inst_958_, v_m_959_, v_a_960_, v_fallback_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_m_965_, lean_object* v_a_966_, lean_object* v_fallback_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_963_, v_inst_964_, v_m_965_, v_a_966_, v_fallback_967_);
lean_dec(v_fallback_967_);
lean_dec_ref(v_m_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_m_973_, lean_object* v_a_974_, lean_object* v_fallback_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_971_, v_inst_972_, v_m_973_, v_a_974_, v_fallback_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_m_981_, lean_object* v_a_982_, lean_object* v_fallback_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(v_00_u03b1_977_, v_00_u03b2_978_, v_inst_979_, v_inst_980_, v_m_981_, v_a_982_, v_fallback_983_);
lean_dec(v_fallback_983_);
lean_dec_ref(v_m_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_m_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_985_, v_inst_986_, v_inst_987_, v_m_988_, v_a_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_991_, v_inst_992_, v_inst_993_, v_m_994_, v_a_995_);
lean_dec_ref(v_m_994_);
lean_dec(v_inst_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(lean_object* v_00_u03b1_997_, lean_object* v_00_u03b2_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_m_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_999_, v_inst_1000_, v_inst_1001_, v_m_1002_, v_a_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_m_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(v_00_u03b1_1005_, v_00_u03b2_1006_, v_inst_1007_, v_inst_1008_, v_inst_1009_, v_m_1010_, v_a_1011_);
lean_dec_ref(v_m_1010_);
lean_dec(v_inst_1009_);
return v_res_1012_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_noption_none();
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(lean_object* v_f_1014_, lean_object* v_m_1015_){
_start:
{
lean_object* v_keyArray_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_keyArray_1016_ = lean_ctor_get(v_m_1015_, 1);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_array_get_size(v_keyArray_1016_);
v___x_1019_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0);
v___x_1020_ = lean_mk_array(v___x_1018_, v___x_1019_);
lean_inc_ref(v_keyArray_1016_);
v___x_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1017_);
lean_ctor_set(v___x_1021_, 1, v_keyArray_1016_);
lean_ctor_set(v___x_1021_, 2, v___x_1020_);
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v_f_1014_, v_m_1015_, v___x_1021_, v___x_1017_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___boxed(lean_object* v_f_1023_, lean_object* v_m_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_1023_, v_m_1024_);
lean_dec_ref(v_m_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03b2_1027_, lean_object* v_00_u03b4_1028_, lean_object* v_f_1029_, lean_object* v_m_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_1029_, v_m_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___boxed(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_00_u03b4_1034_, lean_object* v_f_1035_, lean_object* v_m_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(v_00_u03b1_1032_, v_00_u03b2_1033_, v_00_u03b4_1034_, v_f_1035_, v_m_1036_);
lean_dec_ref(v_m_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(lean_object* v_m_1038_, lean_object* v_f_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_1039_, v_m_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___boxed(lean_object* v_m_1041_, lean_object* v_f_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(v_m_1041_, v_f_1042_);
lean_dec_ref(v_m_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_00_u03b4_1046_, lean_object* v_m_1047_, lean_object* v_f_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_1048_, v_m_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_00_u03b4_1052_, lean_object* v_m_1053_, lean_object* v_f_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(v_00_u03b1_1050_, v_00_u03b2_1051_, v_00_u03b4_1052_, v_m_1053_, v_f_1054_);
lean_dec_ref(v_m_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_apply_2(v_f_1056_, v_k_1057_, v_v_1058_);
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(lean_object* v_f_1061_, lean_object* v_m_1062_){
_start:
{
lean_object* v_keyArray_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_keyArray_1063_ = lean_ctor_get(v_m_1062_, 1);
v___f_1064_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1064_, 0, v_f_1061_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_array_get_size(v_keyArray_1063_);
v___x_1067_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0);
v___x_1068_ = lean_mk_array(v___x_1066_, v___x_1067_);
lean_inc_ref(v_keyArray_1063_);
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1065_);
lean_ctor_set(v___x_1069_, 1, v_keyArray_1063_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
v___x_1070_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v___f_1064_, v_m_1062_, v___x_1069_, v___x_1065_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg___boxed(lean_object* v_f_1071_, lean_object* v_m_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(v_f_1071_, v_m_1072_);
lean_dec_ref(v_m_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(lean_object* v_m_1074_, lean_object* v_f_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(v_f_1075_, v_m_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___boxed(lean_object* v_m_1077_, lean_object* v_f_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(v_m_1077_, v_f_1078_);
lean_dec_ref(v_m_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_00_u03b4_1082_, lean_object* v_m_1083_, lean_object* v_f_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(v_f_1084_, v_m_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_00_u03b4_1088_, lean_object* v_m_1089_, lean_object* v_f_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_DHashMap_Internal_Raw_u2080_map_u2098(v_00_u03b1_1086_, v_00_u03b2_1087_, v_00_u03b4_1088_, v_m_1089_, v_f_1090_);
lean_dec_ref(v_m_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_00_u03b4_1094_, lean_object* v_f_1095_, lean_object* v_m_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(v_f_1095_, v_m_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_00_u03b4_1100_, lean_object* v_f_1101_, lean_object* v_m_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0(v_00_u03b1_1098_, v_00_u03b2_1099_, v_00_u03b4_1100_, v_f_1101_, v_m_1102_);
lean_dec_ref(v_m_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(lean_object* v_f_1104_, lean_object* v_m_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(v_f_1104_, v_m_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg___boxed(lean_object* v_f_1107_, lean_object* v_m_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_1107_, v_m_1108_);
lean_dec_ref(v_m_1108_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_00_u03b4_1112_, lean_object* v_f_1113_, lean_object* v_m_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0_spec__0___redArg(v_f_1113_, v_m_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_00_u03b4_1118_, lean_object* v_f_1119_, lean_object* v_m_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(v_00_u03b1_1116_, v_00_u03b2_1117_, v_00_u03b4_1118_, v_f_1119_, v_m_1120_);
lean_dec_ref(v_m_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1122_, lean_object* v_k_1123_, lean_object* v_v_1124_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
lean_inc(v_v_1124_);
v___x_1125_ = lean_apply_2(v_f_1122_, v_k_1123_, v_v_1124_);
v___x_1126_ = lean_unbox(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v_v_1124_);
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
else
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_v_1124_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(lean_object* v_f_1129_, lean_object* v_m_1130_){
_start:
{
lean_object* v_keyArray_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_keyArray_1131_ = lean_ctor_get(v_m_1130_, 1);
v___f_1132_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1132_, 0, v_f_1129_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_size(v_keyArray_1131_);
v___x_1135_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg___closed__0);
v___x_1136_ = lean_mk_array(v___x_1134_, v___x_1135_);
lean_inc_ref(v_keyArray_1131_);
v___x_1137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1133_);
lean_ctor_set(v___x_1137_, 1, v_keyArray_1131_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v___f_1132_, v_m_1130_, v___x_1137_, v___x_1133_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg___boxed(lean_object* v_f_1139_, lean_object* v_m_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(v_f_1139_, v_m_1140_);
lean_dec_ref(v_m_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(lean_object* v_m_1142_, lean_object* v_f_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(v_f_1143_, v_m_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___boxed(lean_object* v_m_1145_, lean_object* v_f_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_1145_, v_f_1146_);
lean_dec_ref(v_m_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_m_1150_, lean_object* v_f_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(v_f_1151_, v_m_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_m_1155_, lean_object* v_f_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(v_00_u03b1_1153_, v_00_u03b2_1154_, v_m_1155_, v_f_1156_);
lean_dec_ref(v_m_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0(lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_f_1160_, lean_object* v_m_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(v_f_1160_, v_m_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_f_1165_, lean_object* v_m_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0(v_00_u03b1_1163_, v_00_u03b2_1164_, v_f_1165_, v_m_1166_);
lean_dec_ref(v_m_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(lean_object* v_f_1168_, lean_object* v_m_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(v_f_1168_, v_m_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg___boxed(lean_object* v_f_1171_, lean_object* v_m_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_1171_, v_m_1172_);
lean_dec_ref(v_m_1172_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_f_1176_, lean_object* v_m_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0_spec__0___redArg(v_f_1176_, v_m_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_f_1181_, lean_object* v_m_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(v_00_u03b1_1179_, v_00_u03b2_1180_, v_f_1181_, v_m_1182_);
lean_dec_ref(v_m_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg___lam__0(lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_m_1186_, lean_object* v_p_1187_){
_start:
{
lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___y_1191_; lean_object* v_i_1192_; lean_object* v___y_1198_; lean_object* v___y_1208_; lean_object* v_i_1209_; lean_object* v___x_1224_; 
v_fst_1188_ = lean_ctor_get(v_p_1187_, 0);
lean_inc_n(v_fst_1188_, 2);
v_snd_1189_ = lean_ctor_get(v_p_1187_, 1);
lean_inc(v_snd_1189_);
lean_dec_ref(v_p_1187_);
lean_inc_ref(v_inst_1185_);
lean_inc_ref(v_inst_1184_);
v___x_1224_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1184_, v_inst_1185_, v_m_1186_, v_fst_1188_);
switch(lean_obj_tag(v___x_1224_))
{
case 0:
{
lean_object* v_index_1225_; lean_object* v_size_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
v_index_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_index_1225_);
lean_dec_ref_known(v___x_1224_, 3);
v_size_1226_ = lean_ctor_get(v_m_1186_, 0);
lean_inc(v_size_1226_);
v___x_1227_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1186_, v_size_1226_, v_index_1225_, v_fst_1188_, v_snd_1189_);
lean_dec(v_index_1225_);
return v___x_1227_;
}
case 1:
{
lean_object* v_index_1228_; lean_object* v_size_1229_; lean_object* v_keyArray_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_index_1228_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_index_1228_);
lean_dec_ref_known(v___x_1224_, 1);
v_size_1229_ = lean_ctor_get(v_m_1186_, 0);
v_keyArray_1230_ = lean_ctor_get(v_m_1186_, 1);
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_size_1229_, v___x_1231_);
v___x_1233_ = lean_array_get_size(v_keyArray_1230_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v_index_1228_);
goto v___jp_1214_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1235_ = lean_unsigned_to_nat(4u);
v___x_1236_ = lean_nat_mul(v___x_1232_, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(3u);
v___x_1238_ = lean_nat_mul(v___x_1233_, v___x_1237_);
v___x_1239_ = lean_nat_dec_le(v___x_1236_, v___x_1238_);
lean_dec(v___x_1238_);
lean_dec(v___x_1236_);
if (v___x_1239_ == 0)
{
lean_dec(v___x_1232_);
lean_dec(v_index_1228_);
goto v___jp_1214_;
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
v___x_1240_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1186_, v___x_1232_, v_index_1228_, v_fst_1188_, v_snd_1189_);
lean_dec(v_index_1228_);
return v___x_1240_;
}
}
}
default: 
{
lean_object* v_size_1241_; lean_object* v_keyArray_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_size_1241_ = lean_ctor_get(v_m_1186_, 0);
v_keyArray_1242_ = lean_ctor_get(v_m_1186_, 1);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_size_1241_, v___x_1243_);
v___x_1245_ = lean_array_get_size(v_keyArray_1242_);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_dec(v___x_1244_);
lean_inc_ref(v_inst_1185_);
lean_inc_ref(v_inst_1184_);
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1184_, v_inst_1185_, v_m_1186_);
v___y_1198_ = v___x_1247_;
goto v___jp_1197_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1248_ = lean_unsigned_to_nat(4u);
v___x_1249_ = lean_nat_mul(v___x_1244_, v___x_1248_);
lean_dec(v___x_1244_);
v___x_1250_ = lean_unsigned_to_nat(3u);
v___x_1251_ = lean_nat_mul(v___x_1245_, v___x_1250_);
v___x_1252_ = lean_nat_dec_le(v___x_1249_, v___x_1251_);
lean_dec(v___x_1251_);
lean_dec(v___x_1249_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_inc_ref(v_inst_1185_);
lean_inc_ref(v_inst_1184_);
v___x_1253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1184_, v_inst_1185_, v_m_1186_);
v___y_1198_ = v___x_1253_;
goto v___jp_1197_;
}
else
{
v___y_1198_ = v_m_1186_;
goto v___jp_1197_;
}
}
}
}
v___jp_1190_:
{
lean_object* v_size_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_size_1193_ = lean_ctor_get(v___y_1191_, 0);
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_size_1193_, v___x_1194_);
v___x_1196_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1191_, v___x_1195_, v_i_1192_, v_fst_1188_, v_snd_1189_);
lean_dec(v_i_1192_);
return v___x_1196_;
}
v___jp_1197_:
{
lean_object* v___x_1199_; 
lean_inc(v_fst_1188_);
v___x_1199_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1184_, v_inst_1185_, v___y_1198_, v_fst_1188_);
switch(lean_obj_tag(v___x_1199_))
{
case 0:
{
lean_object* v_index_1200_; lean_object* v_size_1201_; lean_object* v___x_1202_; 
v_index_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_index_1200_);
lean_dec_ref_known(v___x_1199_, 3);
v_size_1201_ = lean_ctor_get(v___y_1198_, 0);
lean_inc(v_size_1201_);
v___x_1202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1198_, v_size_1201_, v_index_1200_, v_fst_1188_, v_snd_1189_);
lean_dec(v_index_1200_);
return v___x_1202_;
}
case 1:
{
lean_object* v_index_1203_; 
v_index_1203_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_index_1203_);
lean_dec_ref_known(v___x_1199_, 1);
v___y_1191_ = v___y_1198_;
v_i_1192_ = v_index_1203_;
goto v___jp_1190_;
}
default: 
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1198_, v___x_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_index_1206_; 
v_index_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_index_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___y_1191_ = v___y_1198_;
v_i_1192_ = v_index_1206_;
goto v___jp_1190_;
}
else
{
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
return v___y_1198_;
}
}
}
}
v___jp_1207_:
{
lean_object* v_size_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_size_1210_ = lean_ctor_get(v___y_1208_, 0);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_add(v_size_1210_, v___x_1211_);
v___x_1213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1208_, v___x_1212_, v_i_1209_, v_fst_1188_, v_snd_1189_);
lean_dec(v_i_1209_);
return v___x_1213_;
}
v___jp_1214_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_inc_ref(v_inst_1185_);
lean_inc_ref(v_inst_1184_);
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1184_, v_inst_1185_, v_m_1186_);
lean_inc(v_fst_1188_);
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1184_, v_inst_1185_, v___x_1215_, v_fst_1188_);
switch(lean_obj_tag(v___x_1216_))
{
case 0:
{
lean_object* v_index_1217_; lean_object* v_size_1218_; lean_object* v___x_1219_; 
v_index_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_index_1217_);
lean_dec_ref_known(v___x_1216_, 3);
v_size_1218_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_size_1218_);
v___x_1219_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1215_, v_size_1218_, v_index_1217_, v_fst_1188_, v_snd_1189_);
lean_dec(v_index_1217_);
return v___x_1219_;
}
case 1:
{
lean_object* v_index_1220_; 
v_index_1220_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_index_1220_);
lean_dec_ref_known(v___x_1216_, 1);
v___y_1208_ = v___x_1215_;
v_i_1209_ = v_index_1220_;
goto v___jp_1207_;
}
default: 
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1215_, v___x_1221_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_index_1223_; 
v_index_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_index_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___y_1208_ = v___x_1215_;
v_i_1209_ = v_index_1223_;
goto v___jp_1207_;
}
else
{
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_m_1256_, lean_object* v_l_1257_){
_start:
{
lean_object* v___f_1258_; lean_object* v___x_1259_; 
v___f_1258_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1258_, 0, v_inst_1254_);
lean_closure_set(v___f_1258_, 1, v_inst_1255_);
v___x_1259_ = l_List_foldl___redArg(v___f_1258_, v_m_1256_, v_l_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_m_1264_, lean_object* v_l_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(v_inst_1262_, v_inst_1263_, v_m_1264_, v_l_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_m_1269_, lean_object* v_l_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_erase), 6, 4);
lean_closure_set(v___x_1271_, 0, lean_box(0));
lean_closure_set(v___x_1271_, 1, lean_box(0));
lean_closure_set(v___x_1271_, 2, v_inst_1267_);
lean_closure_set(v___x_1271_, 3, v_inst_1268_);
v___x_1272_ = l_List_foldl___redArg(v___x_1271_, v_m_1269_, v_l_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_m_1277_, lean_object* v_l_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(v_inst_1275_, v_inst_1276_, v_m_1277_, v_l_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg___lam__0(lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_m_1282_, lean_object* v_p_1283_){
_start:
{
lean_object* v_fst_1284_; lean_object* v_snd_1285_; lean_object* v___y_1287_; lean_object* v_i_1288_; lean_object* v___y_1294_; lean_object* v___y_1304_; lean_object* v_i_1305_; lean_object* v___x_1320_; 
v_fst_1284_ = lean_ctor_get(v_p_1283_, 0);
lean_inc_n(v_fst_1284_, 2);
v_snd_1285_ = lean_ctor_get(v_p_1283_, 1);
lean_inc(v_snd_1285_);
lean_dec_ref(v_p_1283_);
lean_inc_ref(v_inst_1281_);
lean_inc_ref(v_inst_1280_);
v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1280_, v_inst_1281_, v_m_1282_, v_fst_1284_);
switch(lean_obj_tag(v___x_1320_))
{
case 0:
{
lean_dec_ref_known(v___x_1320_, 3);
lean_dec(v_snd_1285_);
lean_dec(v_fst_1284_);
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
return v_m_1282_;
}
case 1:
{
lean_object* v_index_1321_; lean_object* v_size_1322_; lean_object* v_keyArray_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_index_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_index_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v_size_1322_ = lean_ctor_get(v_m_1282_, 0);
v_keyArray_1323_ = lean_ctor_get(v_m_1282_, 1);
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_nat_add(v_size_1322_, v___x_1324_);
v___x_1326_ = lean_array_get_size(v_keyArray_1323_);
v___x_1327_ = lean_nat_dec_lt(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_dec(v___x_1325_);
lean_dec(v_index_1321_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1328_ = lean_unsigned_to_nat(4u);
v___x_1329_ = lean_nat_mul(v___x_1325_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_nat_mul(v___x_1326_, v___x_1330_);
v___x_1332_ = lean_nat_dec_le(v___x_1329_, v___x_1331_);
lean_dec(v___x_1331_);
lean_dec(v___x_1329_);
if (v___x_1332_ == 0)
{
lean_dec(v___x_1325_);
lean_dec(v_index_1321_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1333_; 
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
v___x_1333_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1282_, v___x_1325_, v_index_1321_, v_fst_1284_, v_snd_1285_);
lean_dec(v_index_1321_);
return v___x_1333_;
}
}
}
default: 
{
lean_object* v_size_1334_; lean_object* v_keyArray_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_size_1334_ = lean_ctor_get(v_m_1282_, 0);
v_keyArray_1335_ = lean_ctor_get(v_m_1282_, 1);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_size_1334_, v___x_1336_);
v___x_1338_ = lean_array_get_size(v_keyArray_1335_);
v___x_1339_ = lean_nat_dec_lt(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec(v___x_1337_);
lean_inc_ref(v_inst_1281_);
lean_inc_ref(v_inst_1280_);
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1280_, v_inst_1281_, v_m_1282_);
v___y_1294_ = v___x_1340_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1341_ = lean_unsigned_to_nat(4u);
v___x_1342_ = lean_nat_mul(v___x_1337_, v___x_1341_);
lean_dec(v___x_1337_);
v___x_1343_ = lean_unsigned_to_nat(3u);
v___x_1344_ = lean_nat_mul(v___x_1338_, v___x_1343_);
v___x_1345_ = lean_nat_dec_le(v___x_1342_, v___x_1344_);
lean_dec(v___x_1344_);
lean_dec(v___x_1342_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_inc_ref(v_inst_1281_);
lean_inc_ref(v_inst_1280_);
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1280_, v_inst_1281_, v_m_1282_);
v___y_1294_ = v___x_1346_;
goto v___jp_1293_;
}
else
{
v___y_1294_ = v_m_1282_;
goto v___jp_1293_;
}
}
}
}
v___jp_1286_:
{
lean_object* v_size_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_size_1289_ = lean_ctor_get(v___y_1287_, 0);
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_add(v_size_1289_, v___x_1290_);
v___x_1292_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1287_, v___x_1291_, v_i_1288_, v_fst_1284_, v_snd_1285_);
lean_dec(v_i_1288_);
return v___x_1292_;
}
v___jp_1293_:
{
lean_object* v___x_1295_; 
lean_inc(v_fst_1284_);
v___x_1295_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1280_, v_inst_1281_, v___y_1294_, v_fst_1284_);
switch(lean_obj_tag(v___x_1295_))
{
case 0:
{
lean_object* v_index_1296_; lean_object* v_size_1297_; lean_object* v___x_1298_; 
v_index_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_index_1296_);
lean_dec_ref_known(v___x_1295_, 3);
v_size_1297_ = lean_ctor_get(v___y_1294_, 0);
lean_inc(v_size_1297_);
v___x_1298_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1294_, v_size_1297_, v_index_1296_, v_fst_1284_, v_snd_1285_);
lean_dec(v_index_1296_);
return v___x_1298_;
}
case 1:
{
lean_object* v_index_1299_; 
v_index_1299_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_index_1299_);
lean_dec_ref_known(v___x_1295_, 1);
v___y_1287_ = v___y_1294_;
v_i_1288_ = v_index_1299_;
goto v___jp_1286_;
}
default: 
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1294_, v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_index_1302_; 
v_index_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_index_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___y_1287_ = v___y_1294_;
v_i_1288_ = v_index_1302_;
goto v___jp_1286_;
}
else
{
lean_dec(v_snd_1285_);
lean_dec(v_fst_1284_);
return v___y_1294_;
}
}
}
}
v___jp_1303_:
{
lean_object* v_size_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_size_1306_ = lean_ctor_get(v___y_1304_, 0);
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_add(v_size_1306_, v___x_1307_);
v___x_1309_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1304_, v___x_1308_, v_i_1305_, v_fst_1284_, v_snd_1285_);
lean_dec(v_i_1305_);
return v___x_1309_;
}
v___jp_1310_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_inc_ref(v_inst_1281_);
lean_inc_ref(v_inst_1280_);
v___x_1311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1280_, v_inst_1281_, v_m_1282_);
lean_inc(v_fst_1284_);
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1280_, v_inst_1281_, v___x_1311_, v_fst_1284_);
switch(lean_obj_tag(v___x_1312_))
{
case 0:
{
lean_object* v_index_1313_; lean_object* v_size_1314_; lean_object* v___x_1315_; 
v_index_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_index_1313_);
lean_dec_ref_known(v___x_1312_, 3);
v_size_1314_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_size_1314_);
v___x_1315_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1311_, v_size_1314_, v_index_1313_, v_fst_1284_, v_snd_1285_);
lean_dec(v_index_1313_);
return v___x_1315_;
}
case 1:
{
lean_object* v_index_1316_; 
v_index_1316_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_index_1316_);
lean_dec_ref_known(v___x_1312_, 1);
v___y_1304_ = v___x_1311_;
v_i_1305_ = v_index_1316_;
goto v___jp_1303_;
}
default: 
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1311_, v___x_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_index_1319_; 
v_index_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_index_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___y_1304_ = v___x_1311_;
v_i_1305_ = v_index_1319_;
goto v___jp_1303_;
}
else
{
lean_dec(v_snd_1285_);
lean_dec(v_fst_1284_);
return v___x_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_m_1349_, lean_object* v_l_1350_){
_start:
{
lean_object* v___f_1351_; lean_object* v___x_1352_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1351_, 0, v_inst_1347_);
lean_closure_set(v___f_1351_, 1, v_inst_1348_);
v___x_1352_ = l_List_foldl___redArg(v___f_1351_, v_m_1349_, v_l_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_m_1357_, lean_object* v_l_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1355_, v_inst_1356_, v_m_1357_, v_l_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_m_u2082_1362_, uint8_t v___x_1363_, lean_object* v_k_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1360_, v_inst_1361_, v_m_u2082_1362_, v_k_1364_);
if (v___x_1366_ == 0)
{
return v___x_1363_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = 0;
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_m_u2082_1370_, lean_object* v___x_1371_, lean_object* v_k_1372_, lean_object* v_x_1373_){
_start:
{
uint8_t v___x_44__boxed_1374_; uint8_t v_res_1375_; lean_object* v_r_1376_; 
v___x_44__boxed_1374_ = lean_unbox(v___x_1371_);
v_res_1375_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(v_inst_1368_, v_inst_1369_, v_m_u2082_1370_, v___x_44__boxed_1374_, v_k_1372_, v_x_1373_);
lean_dec(v_x_1373_);
lean_dec_ref(v_m_u2082_1370_);
v_r_1376_ = lean_box(v_res_1375_);
return v_r_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_m_u2081_1400_, lean_object* v_m_u2082_1401_){
_start:
{
lean_object* v_size_1402_; lean_object* v_size_1403_; uint8_t v___x_1404_; 
v_size_1402_ = lean_ctor_get(v_m_u2081_1400_, 0);
v_size_1403_ = lean_ctor_get(v_m_u2082_1401_, 0);
v___x_1404_ = lean_nat_dec_le(v_size_1402_, v_size_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___f_1405_; lean_object* v___x_1406_; 
v___f_1405_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10));
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1405_, v_inst_1398_, v_inst_1399_, v_m_u2081_1400_, v_m_u2082_1401_);
return v___x_1406_;
}
else
{
lean_object* v___x_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; 
v___x_1407_ = lean_box(v___x_1404_);
v___f_1408_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1408_, 0, v_inst_1398_);
lean_closure_set(v___f_1408_, 1, v_inst_1399_);
lean_closure_set(v___f_1408_, 2, v_m_u2082_1401_);
lean_closure_set(v___f_1408_, 3, v___x_1407_);
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1408_, v_m_u2081_1400_);
lean_dec_ref(v_m_u2081_1400_);
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(lean_object* v_00_u03b1_1410_, lean_object* v_00_u03b2_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_m_u2081_1414_, lean_object* v_m_u2082_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(v_inst_1412_, v_inst_1413_, v_m_u2081_1414_, v_m_u2082_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg___lam__0(lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_a_1419_, lean_object* v_b_1420_, lean_object* v_acc_1421_){
_start:
{
lean_object* v___y_1423_; lean_object* v_i_1424_; lean_object* v___y_1443_; lean_object* v_i_1444_; lean_object* v___y_1451_; lean_object* v___x_1462_; 
lean_inc(v_a_1419_);
lean_inc_ref(v_inst_1418_);
lean_inc_ref(v_inst_1417_);
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1417_, v_inst_1418_, v_acc_1421_, v_a_1419_);
switch(lean_obj_tag(v___x_1462_))
{
case 0:
{
lean_object* v___x_1463_; 
lean_dec_ref_known(v___x_1462_, 3);
lean_dec(v_b_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_inst_1418_);
lean_dec_ref(v_inst_1417_);
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_acc_1421_);
return v___x_1463_;
}
case 1:
{
lean_object* v_index_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1483_; 
v_index_1464_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1466_ = v___x_1462_;
v_isShared_1467_ = v_isSharedCheck_1483_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_index_1464_);
lean_dec(v___x_1462_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1483_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_size_1468_; lean_object* v_keyArray_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_size_1468_ = lean_ctor_get(v_acc_1421_, 0);
v_keyArray_1469_ = lean_ctor_get(v_acc_1421_, 1);
v___x_1470_ = lean_unsigned_to_nat(1u);
v___x_1471_ = lean_nat_add(v_size_1468_, v___x_1470_);
v___x_1472_ = lean_array_get_size(v_keyArray_1469_);
v___x_1473_ = lean_nat_dec_lt(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_dec(v___x_1471_);
lean_del_object(v___x_1466_);
lean_dec(v_index_1464_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1474_ = lean_unsigned_to_nat(4u);
v___x_1475_ = lean_nat_mul(v___x_1471_, v___x_1474_);
v___x_1476_ = lean_unsigned_to_nat(3u);
v___x_1477_ = lean_nat_mul(v___x_1472_, v___x_1476_);
v___x_1478_ = lean_nat_dec_le(v___x_1475_, v___x_1477_);
lean_dec(v___x_1477_);
lean_dec(v___x_1475_);
if (v___x_1478_ == 0)
{
lean_dec(v___x_1471_);
lean_del_object(v___x_1466_);
lean_dec(v_index_1464_);
goto v___jp_1430_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_dec_ref(v_inst_1418_);
lean_dec_ref(v_inst_1417_);
v___x_1479_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1421_, v___x_1471_, v_index_1464_, v_a_1419_, v_b_1420_);
lean_dec(v_index_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1479_);
v___x_1481_ = v___x_1466_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
default: 
{
lean_object* v_size_1484_; lean_object* v_keyArray_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_size_1484_ = lean_ctor_get(v_acc_1421_, 0);
v_keyArray_1485_ = lean_ctor_get(v_acc_1421_, 1);
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v_size_1484_, v___x_1486_);
v___x_1488_ = lean_array_get_size(v_keyArray_1485_);
v___x_1489_ = lean_nat_dec_lt(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec(v___x_1487_);
lean_inc_ref(v_inst_1418_);
lean_inc_ref(v_inst_1417_);
v___x_1490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1417_, v_inst_1418_, v_acc_1421_);
v___y_1451_ = v___x_1490_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1491_ = lean_unsigned_to_nat(4u);
v___x_1492_ = lean_nat_mul(v___x_1487_, v___x_1491_);
lean_dec(v___x_1487_);
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_nat_mul(v___x_1488_, v___x_1493_);
v___x_1495_ = lean_nat_dec_le(v___x_1492_, v___x_1494_);
lean_dec(v___x_1494_);
lean_dec(v___x_1492_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
lean_inc_ref(v_inst_1418_);
lean_inc_ref(v_inst_1417_);
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1417_, v_inst_1418_, v_acc_1421_);
v___y_1451_ = v___x_1496_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v_acc_1421_;
goto v___jp_1450_;
}
}
}
}
v___jp_1422_:
{
lean_object* v_size_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_size_1425_ = lean_ctor_get(v___y_1423_, 0);
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = lean_nat_add(v_size_1425_, v___x_1426_);
v___x_1428_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1423_, v___x_1427_, v_i_1424_, v_a_1419_, v_b_1420_);
lean_dec(v_i_1424_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
v___jp_1430_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_inc_ref(v_inst_1418_);
lean_inc_ref(v_inst_1417_);
v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1417_, v_inst_1418_, v_acc_1421_);
lean_inc(v_a_1419_);
v___x_1432_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1417_, v_inst_1418_, v___x_1431_, v_a_1419_);
switch(lean_obj_tag(v___x_1432_))
{
case 0:
{
lean_object* v_index_1433_; lean_object* v_size_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_index_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_index_1433_);
lean_dec_ref_known(v___x_1432_, 3);
v_size_1434_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_size_1434_);
v___x_1435_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1431_, v_size_1434_, v_index_1433_, v_a_1419_, v_b_1420_);
lean_dec(v_index_1433_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
case 1:
{
lean_object* v_index_1437_; 
v_index_1437_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_index_1437_);
lean_dec_ref_known(v___x_1432_, 1);
v___y_1423_ = v___x_1431_;
v_i_1424_ = v_index_1437_;
goto v___jp_1422_;
}
default: 
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1431_, v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_index_1440_; 
v_index_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_index_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___y_1423_ = v___x_1431_;
v_i_1424_ = v_index_1440_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_b_1420_);
lean_dec(v_a_1419_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1431_);
return v___x_1441_;
}
}
}
}
v___jp_1442_:
{
lean_object* v_size_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_size_1445_ = lean_ctor_get(v___y_1443_, 0);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_size_1445_, v___x_1446_);
v___x_1448_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1443_, v___x_1447_, v_i_1444_, v_a_1419_, v_b_1420_);
lean_dec(v_i_1444_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
v___jp_1450_:
{
lean_object* v___x_1452_; 
lean_inc(v_a_1419_);
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1417_, v_inst_1418_, v___y_1451_, v_a_1419_);
switch(lean_obj_tag(v___x_1452_))
{
case 0:
{
lean_object* v_index_1453_; lean_object* v_size_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_index_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_index_1453_);
lean_dec_ref_known(v___x_1452_, 3);
v_size_1454_ = lean_ctor_get(v___y_1451_, 0);
lean_inc(v_size_1454_);
v___x_1455_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1451_, v_size_1454_, v_index_1453_, v_a_1419_, v_b_1420_);
lean_dec(v_index_1453_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
case 1:
{
lean_object* v_index_1457_; 
v_index_1457_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_index_1457_);
lean_dec_ref_known(v___x_1452_, 1);
v___y_1443_ = v___y_1451_;
v_i_1444_ = v_index_1457_;
goto v___jp_1442_;
}
default: 
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1451_, v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_index_1460_; 
v_index_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_index_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___y_1443_ = v___y_1451_;
v_i_1444_ = v_index_1460_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_b_1420_);
lean_dec(v_a_1419_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1451_);
return v___x_1461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_m_u2081_1499_, lean_object* v_m_u2082_1500_){
_start:
{
lean_object* v_size_1501_; lean_object* v_size_1502_; uint8_t v___x_1503_; 
v_size_1501_ = lean_ctor_get(v_m_u2081_1499_, 0);
v_size_1502_ = lean_ctor_get(v_m_u2082_1500_, 0);
v___x_1503_ = lean_nat_dec_le(v_size_1501_, v_size_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___f_1504_; lean_object* v___x_1505_; 
v___f_1504_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10));
v___x_1505_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1504_, v_inst_1497_, v_inst_1498_, v_m_u2081_1499_, v_m_u2082_1500_);
return v___x_1505_;
}
else
{
lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___f_1506_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1506_, 0, v_inst_1497_);
lean_closure_set(v___f_1506_, 1, v_inst_1498_);
v___x_1507_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9));
v___x_1508_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1507_, v___f_1506_, v_m_u2082_1500_, v_m_u2081_1499_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_m_u2081_1513_, lean_object* v_m_u2082_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(v_inst_1511_, v_inst_1512_, v_m_u2081_1513_, v_m_u2082_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_m_1518_, lean_object* v_sofar_1519_, lean_object* v_k_1520_){
_start:
{
lean_object* v___x_1521_; 
lean_inc_ref(v_inst_1517_);
lean_inc_ref(v_inst_1516_);
v___x_1521_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1516_, v_inst_1517_, v_m_1518_, v_k_1520_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_dec_ref(v_inst_1517_);
lean_dec_ref(v_inst_1516_);
return v_sofar_1519_;
}
else
{
lean_object* v_val_1522_; lean_object* v_fst_1523_; lean_object* v_snd_1524_; lean_object* v___y_1526_; lean_object* v_i_1527_; lean_object* v___y_1533_; lean_object* v___y_1543_; lean_object* v_i_1544_; lean_object* v___x_1559_; 
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_fst_1523_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_n(v_fst_1523_, 2);
v_snd_1524_ = lean_ctor_get(v_val_1522_, 1);
lean_inc(v_snd_1524_);
lean_dec(v_val_1522_);
lean_inc_ref(v_inst_1517_);
lean_inc_ref(v_inst_1516_);
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1516_, v_inst_1517_, v_sofar_1519_, v_fst_1523_);
switch(lean_obj_tag(v___x_1559_))
{
case 0:
{
lean_object* v_index_1560_; lean_object* v_size_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_inst_1517_);
lean_dec_ref(v_inst_1516_);
v_index_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_index_1560_);
lean_dec_ref_known(v___x_1559_, 3);
v_size_1561_ = lean_ctor_get(v_sofar_1519_, 0);
lean_inc(v_size_1561_);
v___x_1562_ = l_Std_DHashMap_Raw_setEntry___redArg(v_sofar_1519_, v_size_1561_, v_index_1560_, v_fst_1523_, v_snd_1524_);
lean_dec(v_index_1560_);
return v___x_1562_;
}
case 1:
{
lean_object* v_index_1563_; lean_object* v_size_1564_; lean_object* v_keyArray_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_index_1563_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_index_1563_);
lean_dec_ref_known(v___x_1559_, 1);
v_size_1564_ = lean_ctor_get(v_sofar_1519_, 0);
v_keyArray_1565_ = lean_ctor_get(v_sofar_1519_, 1);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_add(v_size_1564_, v___x_1566_);
v___x_1568_ = lean_array_get_size(v_keyArray_1565_);
v___x_1569_ = lean_nat_dec_lt(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v___x_1567_);
lean_dec(v_index_1563_);
goto v___jp_1549_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1570_ = lean_unsigned_to_nat(4u);
v___x_1571_ = lean_nat_mul(v___x_1567_, v___x_1570_);
v___x_1572_ = lean_unsigned_to_nat(3u);
v___x_1573_ = lean_nat_mul(v___x_1568_, v___x_1572_);
v___x_1574_ = lean_nat_dec_le(v___x_1571_, v___x_1573_);
lean_dec(v___x_1573_);
lean_dec(v___x_1571_);
if (v___x_1574_ == 0)
{
lean_dec(v___x_1567_);
lean_dec(v_index_1563_);
goto v___jp_1549_;
}
else
{
lean_object* v___x_1575_; 
lean_dec_ref(v_inst_1517_);
lean_dec_ref(v_inst_1516_);
v___x_1575_ = l_Std_DHashMap_Raw_setEntry___redArg(v_sofar_1519_, v___x_1567_, v_index_1563_, v_fst_1523_, v_snd_1524_);
lean_dec(v_index_1563_);
return v___x_1575_;
}
}
}
default: 
{
lean_object* v_size_1576_; lean_object* v_keyArray_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_size_1576_ = lean_ctor_get(v_sofar_1519_, 0);
v_keyArray_1577_ = lean_ctor_get(v_sofar_1519_, 1);
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_size_1576_, v___x_1578_);
v___x_1580_ = lean_array_get_size(v_keyArray_1577_);
v___x_1581_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec(v___x_1579_);
lean_inc_ref(v_inst_1517_);
lean_inc_ref(v_inst_1516_);
v___x_1582_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1516_, v_inst_1517_, v_sofar_1519_);
v___y_1533_ = v___x_1582_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1583_ = lean_unsigned_to_nat(4u);
v___x_1584_ = lean_nat_mul(v___x_1579_, v___x_1583_);
lean_dec(v___x_1579_);
v___x_1585_ = lean_unsigned_to_nat(3u);
v___x_1586_ = lean_nat_mul(v___x_1580_, v___x_1585_);
v___x_1587_ = lean_nat_dec_le(v___x_1584_, v___x_1586_);
lean_dec(v___x_1586_);
lean_dec(v___x_1584_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_inc_ref(v_inst_1517_);
lean_inc_ref(v_inst_1516_);
v___x_1588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1516_, v_inst_1517_, v_sofar_1519_);
v___y_1533_ = v___x_1588_;
goto v___jp_1532_;
}
else
{
v___y_1533_ = v_sofar_1519_;
goto v___jp_1532_;
}
}
}
}
v___jp_1525_:
{
lean_object* v_size_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_size_1528_ = lean_ctor_get(v___y_1526_, 0);
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_nat_add(v_size_1528_, v___x_1529_);
v___x_1531_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1526_, v___x_1530_, v_i_1527_, v_fst_1523_, v_snd_1524_);
lean_dec(v_i_1527_);
return v___x_1531_;
}
v___jp_1532_:
{
lean_object* v___x_1534_; 
lean_inc(v_fst_1523_);
v___x_1534_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1516_, v_inst_1517_, v___y_1533_, v_fst_1523_);
switch(lean_obj_tag(v___x_1534_))
{
case 0:
{
lean_object* v_index_1535_; lean_object* v_size_1536_; lean_object* v___x_1537_; 
v_index_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_index_1535_);
lean_dec_ref_known(v___x_1534_, 3);
v_size_1536_ = lean_ctor_get(v___y_1533_, 0);
lean_inc(v_size_1536_);
v___x_1537_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1533_, v_size_1536_, v_index_1535_, v_fst_1523_, v_snd_1524_);
lean_dec(v_index_1535_);
return v___x_1537_;
}
case 1:
{
lean_object* v_index_1538_; 
v_index_1538_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_index_1538_);
lean_dec_ref_known(v___x_1534_, 1);
v___y_1526_ = v___y_1533_;
v_i_1527_ = v_index_1538_;
goto v___jp_1525_;
}
default: 
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1533_, v___x_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_index_1541_; 
v_index_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_index_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___y_1526_ = v___y_1533_;
v_i_1527_ = v_index_1541_;
goto v___jp_1525_;
}
else
{
lean_dec(v_snd_1524_);
lean_dec(v_fst_1523_);
return v___y_1533_;
}
}
}
}
v___jp_1542_:
{
lean_object* v_size_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_size_1545_ = lean_ctor_get(v___y_1543_, 0);
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v_size_1545_, v___x_1546_);
v___x_1548_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1543_, v___x_1547_, v_i_1544_, v_fst_1523_, v_snd_1524_);
lean_dec(v_i_1544_);
return v___x_1548_;
}
v___jp_1549_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_inc_ref(v_inst_1517_);
lean_inc_ref(v_inst_1516_);
v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1516_, v_inst_1517_, v_sofar_1519_);
lean_inc(v_fst_1523_);
v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1516_, v_inst_1517_, v___x_1550_, v_fst_1523_);
switch(lean_obj_tag(v___x_1551_))
{
case 0:
{
lean_object* v_index_1552_; lean_object* v_size_1553_; lean_object* v___x_1554_; 
v_index_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_index_1552_);
lean_dec_ref_known(v___x_1551_, 3);
v_size_1553_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_size_1553_);
v___x_1554_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1550_, v_size_1553_, v_index_1552_, v_fst_1523_, v_snd_1524_);
lean_dec(v_index_1552_);
return v___x_1554_;
}
case 1:
{
lean_object* v_index_1555_; 
v_index_1555_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_index_1555_);
lean_dec_ref_known(v___x_1551_, 1);
v___y_1543_ = v___x_1550_;
v_i_1544_ = v_index_1555_;
goto v___jp_1542_;
}
default: 
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1550_, v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_index_1558_; 
v_index_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_index_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___y_1543_ = v___x_1550_;
v_i_1544_ = v_index_1558_;
goto v___jp_1542_;
}
else
{
lean_dec(v_snd_1524_);
lean_dec(v_fst_1523_);
return v___x_1550_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_m_1591_, lean_object* v_sofar_1592_, lean_object* v_k_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1589_, v_inst_1590_, v_m_1591_, v_sofar_1592_, v_k_1593_);
lean_dec_ref(v_m_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_m_1599_, lean_object* v_sofar_1600_, lean_object* v_k_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1597_, v_inst_1598_, v_m_1599_, v_sofar_1600_, v_k_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_00_u03b2_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_m_1607_, lean_object* v_sofar_1608_, lean_object* v_k_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(v_00_u03b1_1603_, v_00_u03b2_1604_, v_inst_1605_, v_inst_1606_, v_m_1607_, v_sofar_1608_, v_k_1609_);
lean_dec_ref(v_m_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg___lam__0(lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_m_1613_, lean_object* v_p_1614_){
_start:
{
lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___y_1618_; lean_object* v_i_1619_; lean_object* v___y_1625_; lean_object* v___y_1635_; lean_object* v_i_1636_; lean_object* v___x_1651_; 
v_fst_1615_ = lean_ctor_get(v_p_1614_, 0);
lean_inc_n(v_fst_1615_, 2);
v_snd_1616_ = lean_ctor_get(v_p_1614_, 1);
lean_inc(v_snd_1616_);
lean_dec_ref(v_p_1614_);
lean_inc_ref(v_inst_1612_);
lean_inc_ref(v_inst_1611_);
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1611_, v_inst_1612_, v_m_1613_, v_fst_1615_);
switch(lean_obj_tag(v___x_1651_))
{
case 0:
{
lean_object* v_index_1652_; lean_object* v_size_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v_inst_1612_);
lean_dec_ref(v_inst_1611_);
v_index_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_index_1652_);
lean_dec_ref_known(v___x_1651_, 3);
v_size_1653_ = lean_ctor_get(v_m_1613_, 0);
lean_inc(v_size_1653_);
v___x_1654_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1613_, v_size_1653_, v_index_1652_, v_fst_1615_, v_snd_1616_);
lean_dec(v_index_1652_);
return v___x_1654_;
}
case 1:
{
lean_object* v_index_1655_; lean_object* v_size_1656_; lean_object* v_keyArray_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_index_1655_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_index_1655_);
lean_dec_ref_known(v___x_1651_, 1);
v_size_1656_ = lean_ctor_get(v_m_1613_, 0);
v_keyArray_1657_ = lean_ctor_get(v_m_1613_, 1);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_add(v_size_1656_, v___x_1658_);
v___x_1660_ = lean_array_get_size(v_keyArray_1657_);
v___x_1661_ = lean_nat_dec_lt(v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_dec(v___x_1659_);
lean_dec(v_index_1655_);
goto v___jp_1641_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1662_ = lean_unsigned_to_nat(4u);
v___x_1663_ = lean_nat_mul(v___x_1659_, v___x_1662_);
v___x_1664_ = lean_unsigned_to_nat(3u);
v___x_1665_ = lean_nat_mul(v___x_1660_, v___x_1664_);
v___x_1666_ = lean_nat_dec_le(v___x_1663_, v___x_1665_);
lean_dec(v___x_1665_);
lean_dec(v___x_1663_);
if (v___x_1666_ == 0)
{
lean_dec(v___x_1659_);
lean_dec(v_index_1655_);
goto v___jp_1641_;
}
else
{
lean_object* v___x_1667_; 
lean_dec_ref(v_inst_1612_);
lean_dec_ref(v_inst_1611_);
v___x_1667_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1613_, v___x_1659_, v_index_1655_, v_fst_1615_, v_snd_1616_);
lean_dec(v_index_1655_);
return v___x_1667_;
}
}
}
default: 
{
lean_object* v_size_1668_; lean_object* v_keyArray_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_size_1668_ = lean_ctor_get(v_m_1613_, 0);
v_keyArray_1669_ = lean_ctor_get(v_m_1613_, 1);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_add(v_size_1668_, v___x_1670_);
v___x_1672_ = lean_array_get_size(v_keyArray_1669_);
v___x_1673_ = lean_nat_dec_lt(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec(v___x_1671_);
lean_inc_ref(v_inst_1612_);
lean_inc_ref(v_inst_1611_);
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1611_, v_inst_1612_, v_m_1613_);
v___y_1625_ = v___x_1674_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1675_ = lean_unsigned_to_nat(4u);
v___x_1676_ = lean_nat_mul(v___x_1671_, v___x_1675_);
lean_dec(v___x_1671_);
v___x_1677_ = lean_unsigned_to_nat(3u);
v___x_1678_ = lean_nat_mul(v___x_1672_, v___x_1677_);
v___x_1679_ = lean_nat_dec_le(v___x_1676_, v___x_1678_);
lean_dec(v___x_1678_);
lean_dec(v___x_1676_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
lean_inc_ref(v_inst_1612_);
lean_inc_ref(v_inst_1611_);
v___x_1680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1611_, v_inst_1612_, v_m_1613_);
v___y_1625_ = v___x_1680_;
goto v___jp_1624_;
}
else
{
v___y_1625_ = v_m_1613_;
goto v___jp_1624_;
}
}
}
}
v___jp_1617_:
{
lean_object* v_size_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_size_1620_ = lean_ctor_get(v___y_1618_, 0);
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_nat_add(v_size_1620_, v___x_1621_);
v___x_1623_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1618_, v___x_1622_, v_i_1619_, v_fst_1615_, v_snd_1616_);
lean_dec(v_i_1619_);
return v___x_1623_;
}
v___jp_1624_:
{
lean_object* v___x_1626_; 
lean_inc(v_fst_1615_);
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1611_, v_inst_1612_, v___y_1625_, v_fst_1615_);
switch(lean_obj_tag(v___x_1626_))
{
case 0:
{
lean_object* v_index_1627_; lean_object* v_size_1628_; lean_object* v___x_1629_; 
v_index_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_index_1627_);
lean_dec_ref_known(v___x_1626_, 3);
v_size_1628_ = lean_ctor_get(v___y_1625_, 0);
lean_inc(v_size_1628_);
v___x_1629_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1625_, v_size_1628_, v_index_1627_, v_fst_1615_, v_snd_1616_);
lean_dec(v_index_1627_);
return v___x_1629_;
}
case 1:
{
lean_object* v_index_1630_; 
v_index_1630_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_index_1630_);
lean_dec_ref_known(v___x_1626_, 1);
v___y_1618_ = v___y_1625_;
v_i_1619_ = v_index_1630_;
goto v___jp_1617_;
}
default: 
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1625_, v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_index_1633_; 
v_index_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_index_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___y_1618_ = v___y_1625_;
v_i_1619_ = v_index_1633_;
goto v___jp_1617_;
}
else
{
lean_dec(v_snd_1616_);
lean_dec(v_fst_1615_);
return v___y_1625_;
}
}
}
}
v___jp_1634_:
{
lean_object* v_size_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_size_1637_ = lean_ctor_get(v___y_1635_, 0);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_size_1637_, v___x_1638_);
v___x_1640_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1635_, v___x_1639_, v_i_1636_, v_fst_1615_, v_snd_1616_);
lean_dec(v_i_1636_);
return v___x_1640_;
}
v___jp_1641_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_inc_ref(v_inst_1612_);
lean_inc_ref(v_inst_1611_);
v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1611_, v_inst_1612_, v_m_1613_);
lean_inc(v_fst_1615_);
v___x_1643_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1611_, v_inst_1612_, v___x_1642_, v_fst_1615_);
switch(lean_obj_tag(v___x_1643_))
{
case 0:
{
lean_object* v_index_1644_; lean_object* v_size_1645_; lean_object* v___x_1646_; 
v_index_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_index_1644_);
lean_dec_ref_known(v___x_1643_, 3);
v_size_1645_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_size_1645_);
v___x_1646_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1642_, v_size_1645_, v_index_1644_, v_fst_1615_, v_snd_1616_);
lean_dec(v_index_1644_);
return v___x_1646_;
}
case 1:
{
lean_object* v_index_1647_; 
v_index_1647_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_index_1647_);
lean_dec_ref_known(v___x_1643_, 1);
v___y_1635_ = v___x_1642_;
v_i_1636_ = v_index_1647_;
goto v___jp_1634_;
}
default: 
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1642_, v___x_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_index_1650_; 
v_index_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_index_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___y_1635_ = v___x_1642_;
v_i_1636_ = v_index_1650_;
goto v___jp_1634_;
}
else
{
lean_dec(v_snd_1616_);
lean_dec(v_fst_1615_);
return v___x_1642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_m_1683_, lean_object* v_l_1684_){
_start:
{
lean_object* v___f_1685_; lean_object* v___x_1686_; 
v___f_1685_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1685_, 0, v_inst_1681_);
lean_closure_set(v___f_1685_, 1, v_inst_1682_);
v___x_1686_ = l_List_foldl___redArg(v___f_1685_, v_m_1683_, v_l_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(lean_object* v_00_u03b1_1687_, lean_object* v_00_u03b2_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_m_1691_, lean_object* v_l_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(v_inst_1689_, v_inst_1690_, v_m_1691_, v_l_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg___lam__0(lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_m_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___y_1700_; lean_object* v_i_1701_; lean_object* v___y_1707_; lean_object* v___y_1717_; lean_object* v_i_1718_; lean_object* v___x_1733_; 
v___x_1698_ = lean_box(0);
lean_inc(v_a_1697_);
lean_inc_ref(v_inst_1695_);
lean_inc_ref(v_inst_1694_);
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1694_, v_inst_1695_, v_m_1696_, v_a_1697_);
switch(lean_obj_tag(v___x_1733_))
{
case 0:
{
lean_dec_ref_known(v___x_1733_, 3);
lean_dec(v_a_1697_);
lean_dec_ref(v_inst_1695_);
lean_dec_ref(v_inst_1694_);
return v_m_1696_;
}
case 1:
{
lean_object* v_index_1734_; lean_object* v_size_1735_; lean_object* v_keyArray_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_index_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_index_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v_size_1735_ = lean_ctor_get(v_m_1696_, 0);
v_keyArray_1736_ = lean_ctor_get(v_m_1696_, 1);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_size_1735_, v___x_1737_);
v___x_1739_ = lean_array_get_size(v_keyArray_1736_);
v___x_1740_ = lean_nat_dec_lt(v___x_1738_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_dec(v___x_1738_);
lean_dec(v_index_1734_);
goto v___jp_1723_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1741_ = lean_unsigned_to_nat(4u);
v___x_1742_ = lean_nat_mul(v___x_1738_, v___x_1741_);
v___x_1743_ = lean_unsigned_to_nat(3u);
v___x_1744_ = lean_nat_mul(v___x_1739_, v___x_1743_);
v___x_1745_ = lean_nat_dec_le(v___x_1742_, v___x_1744_);
lean_dec(v___x_1744_);
lean_dec(v___x_1742_);
if (v___x_1745_ == 0)
{
lean_dec(v___x_1738_);
lean_dec(v_index_1734_);
goto v___jp_1723_;
}
else
{
lean_object* v___x_1746_; 
lean_dec_ref(v_inst_1695_);
lean_dec_ref(v_inst_1694_);
v___x_1746_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1696_, v___x_1738_, v_index_1734_, v_a_1697_, v___x_1698_);
lean_dec(v_index_1734_);
return v___x_1746_;
}
}
}
default: 
{
lean_object* v_size_1747_; lean_object* v_keyArray_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_size_1747_ = lean_ctor_get(v_m_1696_, 0);
v_keyArray_1748_ = lean_ctor_get(v_m_1696_, 1);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_size_1747_, v___x_1749_);
v___x_1751_ = lean_array_get_size(v_keyArray_1748_);
v___x_1752_ = lean_nat_dec_lt(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
lean_dec(v___x_1750_);
lean_inc_ref(v_inst_1695_);
lean_inc_ref(v_inst_1694_);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1694_, v_inst_1695_, v_m_1696_);
v___y_1707_ = v___x_1753_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1754_ = lean_unsigned_to_nat(4u);
v___x_1755_ = lean_nat_mul(v___x_1750_, v___x_1754_);
lean_dec(v___x_1750_);
v___x_1756_ = lean_unsigned_to_nat(3u);
v___x_1757_ = lean_nat_mul(v___x_1751_, v___x_1756_);
v___x_1758_ = lean_nat_dec_le(v___x_1755_, v___x_1757_);
lean_dec(v___x_1757_);
lean_dec(v___x_1755_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_inc_ref(v_inst_1695_);
lean_inc_ref(v_inst_1694_);
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1694_, v_inst_1695_, v_m_1696_);
v___y_1707_ = v___x_1759_;
goto v___jp_1706_;
}
else
{
v___y_1707_ = v_m_1696_;
goto v___jp_1706_;
}
}
}
}
v___jp_1699_:
{
lean_object* v_size_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_size_1702_ = lean_ctor_get(v___y_1700_, 0);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_add(v_size_1702_, v___x_1703_);
v___x_1705_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1700_, v___x_1704_, v_i_1701_, v_a_1697_, v___x_1698_);
lean_dec(v_i_1701_);
return v___x_1705_;
}
v___jp_1706_:
{
lean_object* v___x_1708_; 
lean_inc(v_a_1697_);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1694_, v_inst_1695_, v___y_1707_, v_a_1697_);
switch(lean_obj_tag(v___x_1708_))
{
case 0:
{
lean_object* v_index_1709_; lean_object* v_size_1710_; lean_object* v___x_1711_; 
v_index_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_index_1709_);
lean_dec_ref_known(v___x_1708_, 3);
v_size_1710_ = lean_ctor_get(v___y_1707_, 0);
lean_inc(v_size_1710_);
v___x_1711_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1707_, v_size_1710_, v_index_1709_, v_a_1697_, v___x_1698_);
lean_dec(v_index_1709_);
return v___x_1711_;
}
case 1:
{
lean_object* v_index_1712_; 
v_index_1712_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_index_1712_);
lean_dec_ref_known(v___x_1708_, 1);
v___y_1700_ = v___y_1707_;
v_i_1701_ = v_index_1712_;
goto v___jp_1699_;
}
default: 
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_unsigned_to_nat(0u);
v___x_1714_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1707_, v___x_1713_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_index_1715_; 
v_index_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_index_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___y_1700_ = v___y_1707_;
v_i_1701_ = v_index_1715_;
goto v___jp_1699_;
}
else
{
lean_dec(v_a_1697_);
return v___y_1707_;
}
}
}
}
v___jp_1716_:
{
lean_object* v_size_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_size_1719_ = lean_ctor_get(v___y_1717_, 0);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_nat_add(v_size_1719_, v___x_1720_);
v___x_1722_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1717_, v___x_1721_, v_i_1718_, v_a_1697_, v___x_1698_);
lean_dec(v_i_1718_);
return v___x_1722_;
}
v___jp_1723_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_inc_ref(v_inst_1695_);
lean_inc_ref(v_inst_1694_);
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1694_, v_inst_1695_, v_m_1696_);
lean_inc(v_a_1697_);
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1694_, v_inst_1695_, v___x_1724_, v_a_1697_);
switch(lean_obj_tag(v___x_1725_))
{
case 0:
{
lean_object* v_index_1726_; lean_object* v_size_1727_; lean_object* v___x_1728_; 
v_index_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_index_1726_);
lean_dec_ref_known(v___x_1725_, 3);
v_size_1727_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_size_1727_);
v___x_1728_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1724_, v_size_1727_, v_index_1726_, v_a_1697_, v___x_1698_);
lean_dec(v_index_1726_);
return v___x_1728_;
}
case 1:
{
lean_object* v_index_1729_; 
v_index_1729_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_index_1729_);
lean_dec_ref_known(v___x_1725_, 1);
v___y_1717_ = v___x_1724_;
v_i_1718_ = v_index_1729_;
goto v___jp_1716_;
}
default: 
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1724_, v___x_1730_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_index_1732_; 
v_index_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_index_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___y_1717_ = v___x_1724_;
v_i_1718_ = v_index_1732_;
goto v___jp_1716_;
}
else
{
lean_dec(v_a_1697_);
return v___x_1724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_m_1762_, lean_object* v_l_1763_){
_start:
{
lean_object* v___f_1764_; lean_object* v___x_1765_; 
v___f_1764_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1764_, 0, v_inst_1760_);
lean_closure_set(v___f_1764_, 1, v_inst_1761_);
v___x_1765_ = l_List_foldl___redArg(v___f_1764_, v_m_1762_, v_l_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(lean_object* v_00_u03b1_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_m_1769_, lean_object* v_l_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(v_inst_1767_, v_inst_1768_, v_m_1769_, v_l_1770_);
return v___x_1771_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_HashesTo(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_Model(builtin);
}
#ifdef __cplusplus
}
#endif
