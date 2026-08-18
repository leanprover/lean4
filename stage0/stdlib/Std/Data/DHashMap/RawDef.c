// Lean compiler output
// Module: Std.Data.DHashMap.RawDef
// Imports: public import Std.Data.DHashMap.Internal.AssocList.Basic public import Init.Data.Array.Basic public import Init.Data.Erased public import Init.Data.Fin.Fold import Init.Data.Array.Lemmas import Init.ByCases import Init.Classical import Init.Omega import Init.WFTactics
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_noption_some(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_noption_none();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_clearCell___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_clearCell___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_CellsMatch_entry_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_CellsMatch_entry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_cellEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_cellEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_entry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_entry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_entriesFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_entriesFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Raw_fold___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw_fold___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Raw_fold___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_forInFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_forInFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DHashMap_Raw_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw_all___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_match__1_splitter___redArg(lean_object* v_key_1_, lean_object* v_value_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_, lean_object* v_h__4_6_){
_start:
{
uint8_t v_isSome_7_; 
v_isSome_7_ = lean_noption_is_some(v_key_1_);
if (v_isSome_7_ == 0)
{
uint8_t v_isSome_8_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v_isSome_8_ = lean_noption_is_some(v_value_2_);
if (v_isSome_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_h__4_6_);
lean_dec(v_value_2_);
lean_dec(v_key_1_);
v___x_9_ = lean_box(0);
v___x_10_ = lean_apply_1(v_h__1_3_, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
lean_dec(v_h__1_3_);
v___x_11_ = lean_apply_5(v_h__4_6_, v_key_1_, v_value_2_, lean_box(0), lean_box(0), lean_box(0));
return v___x_11_;
}
}
else
{
lean_object* v_val_12_; uint8_t v_isSome_13_; 
lean_dec(v_h__4_6_);
lean_dec(v_h__1_3_);
v_val_12_ = lean_noption_get(v_key_1_);
v_isSome_13_ = lean_noption_is_some(v_value_2_);
if (v_isSome_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec(v_h__3_5_);
lean_dec(v_value_2_);
v___x_14_ = lean_apply_1(v_h__2_4_, v_val_12_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_4_);
v_val_15_ = lean_noption_get(v_value_2_);
v___x_16_ = lean_apply_2(v_h__3_5_, v_val_12_, v_val_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_match__1_splitter(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_motive_19_, lean_object* v_key_20_, lean_object* v_value_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_, lean_object* v_h__3_24_, lean_object* v_h__4_25_){
_start:
{
uint8_t v_isSome_26_; 
v_isSome_26_ = lean_noption_is_some(v_key_20_);
if (v_isSome_26_ == 0)
{
uint8_t v_isSome_27_; 
lean_dec(v_h__3_24_);
lean_dec(v_h__2_23_);
v_isSome_27_ = lean_noption_is_some(v_value_21_);
if (v_isSome_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_h__4_25_);
lean_dec(v_value_21_);
lean_dec(v_key_20_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_apply_1(v_h__1_22_, v___x_28_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; 
lean_dec(v_h__1_22_);
v___x_30_ = lean_apply_5(v_h__4_25_, v_key_20_, v_value_21_, lean_box(0), lean_box(0), lean_box(0));
return v___x_30_;
}
}
else
{
lean_object* v_val_31_; uint8_t v_isSome_32_; 
lean_dec(v_h__4_25_);
lean_dec(v_h__1_22_);
v_val_31_ = lean_noption_get(v_key_20_);
v_isSome_32_ = lean_noption_is_some(v_value_21_);
if (v_isSome_32_ == 0)
{
lean_object* v___x_33_; 
lean_dec(v_h__3_24_);
lean_dec(v_value_21_);
v___x_33_ = lean_apply_1(v_h__2_23_, v_val_31_);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_23_);
v_val_34_ = lean_noption_get(v_value_21_);
v___x_35_ = lean_apply_2(v_h__3_24_, v_val_31_, v_val_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell___redArg(lean_object* v_m_36_, lean_object* v_size_37_, lean_object* v_i_38_, lean_object* v_key_39_, lean_object* v_value_40_){
_start:
{
lean_object* v_keyArray_41_; lean_object* v_valueArray_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_56_; 
v_keyArray_41_ = lean_ctor_get(v_m_36_, 1);
v_valueArray_42_ = lean_ctor_get(v_m_36_, 2);
v_isSharedCheck_56_ = !lean_is_exclusive(v_m_36_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v_m_36_, 0);
lean_dec(v_unused_57_);
v___x_44_ = v_m_36_;
v_isShared_45_ = v_isSharedCheck_56_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_valueArray_42_);
lean_inc(v_keyArray_41_);
lean_dec(v_m_36_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_56_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_array_fset(v_keyArray_41_, v_i_38_, v_key_39_);
v___x_47_ = lean_array_get_size(v_valueArray_42_);
v___x_48_ = lean_nat_dec_lt(v_i_38_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_50_; 
lean_dec(v_value_40_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_46_);
lean_ctor_set(v___x_44_, 0, v_size_37_);
v___x_50_ = v___x_44_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_size_37_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_valueArray_42_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
else
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_array_fset(v_valueArray_42_, v_i_38_, v_value_40_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 2, v___x_52_);
lean_ctor_set(v___x_44_, 1, v___x_46_);
lean_ctor_set(v___x_44_, 0, v_size_37_);
v___x_54_ = v___x_44_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_size_37_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell___redArg___boxed(lean_object* v_m_58_, lean_object* v_size_59_, lean_object* v_i_60_, lean_object* v_key_61_, lean_object* v_value_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_DHashMap_Raw_setCell___redArg(v_m_58_, v_size_59_, v_i_60_, v_key_61_, v_value_62_);
lean_dec(v_i_60_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_m_66_, lean_object* v_size_67_, lean_object* v_i_68_, lean_object* v_hi_69_, lean_object* v_key_70_, lean_object* v_value_71_, lean_object* v_hcell_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_DHashMap_Raw_setCell___redArg(v_m_66_, v_size_67_, v_i_68_, v_key_70_, v_value_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setCell___boxed(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_m_76_, lean_object* v_size_77_, lean_object* v_i_78_, lean_object* v_hi_79_, lean_object* v_key_80_, lean_object* v_value_81_, lean_object* v_hcell_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_DHashMap_Raw_setCell(v_00_u03b1_74_, v_00_u03b2_75_, v_m_76_, v_size_77_, v_i_78_, v_hi_79_, v_key_80_, v_value_81_, v_hcell_82_);
lean_dec(v_i_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object* v_m_84_, lean_object* v_size_85_, lean_object* v_i_86_, lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_noption_some(v_a_87_);
v___x_90_ = lean_noption_some(v_b_88_);
v___x_91_ = l_Std_DHashMap_Raw_setCell___redArg(v_m_84_, v_size_85_, v_i_86_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry___redArg___boxed(lean_object* v_m_92_, lean_object* v_size_93_, lean_object* v_i_94_, lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_92_, v_size_93_, v_i_94_, v_a_95_, v_b_96_);
lean_dec(v_i_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_m_100_, lean_object* v_size_101_, lean_object* v_i_102_, lean_object* v_hi_103_, lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_100_, v_size_101_, v_i_102_, v_a_104_, v_b_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setEntry___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_m_109_, lean_object* v_size_110_, lean_object* v_i_111_, lean_object* v_hi_112_, lean_object* v_a_113_, lean_object* v_b_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_DHashMap_Raw_setEntry(v_00_u03b1_107_, v_00_u03b2_108_, v_m_109_, v_size_110_, v_i_111_, v_hi_112_, v_a_113_, v_b_114_);
lean_dec(v_i_111_);
return v_res_115_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_clearCell___redArg___closed__0(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_noption_none();
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object* v_m_117_, lean_object* v_size_118_, lean_object* v_i_119_){
_start:
{
lean_object* v_keyArray_120_; lean_object* v_valueArray_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_135_; 
v_keyArray_120_ = lean_ctor_get(v_m_117_, 1);
v_valueArray_121_ = lean_ctor_get(v_m_117_, 2);
v_isSharedCheck_135_ = !lean_is_exclusive(v_m_117_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_m_117_, 0);
lean_dec(v_unused_136_);
v___x_123_ = v_m_117_;
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_valueArray_121_);
lean_inc(v_keyArray_120_);
lean_dec(v_m_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_array_get_size(v_valueArray_121_);
v___x_126_ = lean_nat_dec_lt(v_i_119_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_128_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v_size_118_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_size_118_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_keyArray_120_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_valueArray_121_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l_Std_DHashMap_Raw_clearCell___redArg___closed__0, &l_Std_DHashMap_Raw_clearCell___redArg___closed__0_once, _init_l_Std_DHashMap_Raw_clearCell___redArg___closed__0);
v___x_131_ = lean_array_fset(v_valueArray_121_, v_i_119_, v___x_130_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 2, v___x_131_);
lean_ctor_set(v___x_123_, 0, v_size_118_);
v___x_133_ = v___x_123_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_size_118_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_keyArray_120_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell___redArg___boxed(lean_object* v_m_137_, lean_object* v_size_138_, lean_object* v_i_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_137_, v_size_138_, v_i_139_);
lean_dec(v_i_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_m_143_, lean_object* v_size_144_, lean_object* v_i_145_, lean_object* v___hi_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_143_, v_size_144_, v_i_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_clearCell___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_m_150_, lean_object* v_size_151_, lean_object* v_i_152_, lean_object* v___hi_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_DHashMap_Raw_clearCell(v_00_u03b1_148_, v_00_u03b2_149_, v_m_150_, v_size_151_, v_i_152_, v___hi_153_);
lean_dec(v_i_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue___redArg(lean_object* v_m_155_, lean_object* v_size_156_, lean_object* v_i_157_, lean_object* v_b_158_){
_start:
{
lean_object* v_keyArray_159_; lean_object* v_valueArray_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_174_; 
v_keyArray_159_ = lean_ctor_get(v_m_155_, 1);
v_valueArray_160_ = lean_ctor_get(v_m_155_, 2);
v_isSharedCheck_174_ = !lean_is_exclusive(v_m_155_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v_m_155_, 0);
lean_dec(v_unused_175_);
v___x_162_ = v_m_155_;
v_isShared_163_ = v_isSharedCheck_174_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_valueArray_160_);
lean_inc(v_keyArray_159_);
lean_dec(v_m_155_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_174_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_array_get_size(v_valueArray_160_);
v___x_165_ = lean_nat_dec_lt(v_i_157_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_167_; 
lean_dec(v_b_158_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_size_156_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_keyArray_159_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_valueArray_160_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_169_ = lean_noption_some(v_b_158_);
v___x_170_ = lean_array_fset(v_valueArray_160_, v_i_157_, v___x_169_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 2, v___x_170_);
lean_ctor_set(v___x_162_, 0, v_size_156_);
v___x_172_ = v___x_162_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_size_156_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_keyArray_159_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue___redArg___boxed(lean_object* v_m_176_, lean_object* v_size_177_, lean_object* v_i_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DHashMap_Raw_setValue___redArg(v_m_176_, v_size_177_, v_i_178_, v_b_179_);
lean_dec(v_i_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_m_183_, lean_object* v_size_184_, lean_object* v_i_185_, lean_object* v_hi_186_, lean_object* v_a_187_, lean_object* v_hkey_188_, lean_object* v_b_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DHashMap_Raw_setValue___redArg(v_m_183_, v_size_184_, v_i_185_, v_b_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_setValue___boxed(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_m_193_, lean_object* v_size_194_, lean_object* v_i_195_, lean_object* v_hi_196_, lean_object* v_a_197_, lean_object* v_hkey_198_, lean_object* v_b_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DHashMap_Raw_setValue(v_00_u03b1_191_, v_00_u03b2_192_, v_m_193_, v_size_194_, v_i_195_, v_hi_196_, v_a_197_, v_hkey_198_, v_b_199_);
lean_dec(v_a_197_);
lean_dec(v_i_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_CellsMatch_entry_x3f___redArg(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_isSome_203_; 
v_isSome_203_ = lean_noption_is_some(v_x_201_);
if (v_isSome_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_x_202_);
lean_dec(v_x_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
uint8_t v_isSome_205_; 
v_isSome_205_ = lean_noption_is_some(v_x_202_);
if (v_isSome_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec(v_x_202_);
lean_dec(v_x_201_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v_val_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_val_207_ = lean_noption_get(v_x_201_);
v_val_208_ = lean_noption_get(v_x_202_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_val_207_);
lean_ctor_set(v___x_209_, 1, v_val_208_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_CellsMatch_entry_x3f(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
uint8_t v_isSome_216_; 
v_isSome_216_ = lean_noption_is_some(v_x_213_);
if (v_isSome_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec(v_x_214_);
lean_dec(v_x_213_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
uint8_t v_isSome_218_; 
v_isSome_218_ = lean_noption_is_some(v_x_214_);
if (v_isSome_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec(v_x_214_);
lean_dec(v_x_213_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_val_220_; lean_object* v_val_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_val_220_ = lean_noption_get(v_x_213_);
v_val_221_ = lean_noption_get(v_x_214_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_val_220_);
lean_ctor_set(v___x_222_, 1, v_val_221_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_cellEntry_x3f_match__1_splitter___redArg(lean_object* v___key_224_, lean_object* v_value_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
uint8_t v_isSome_228_; 
v_isSome_228_ = lean_noption_is_some(v___key_224_);
if (v_isSome_228_ == 1)
{
uint8_t v_isSome_229_; 
v_isSome_229_ = lean_noption_is_some(v_value_225_);
if (v_isSome_229_ == 1)
{
lean_object* v_val_230_; lean_object* v_val_231_; lean_object* v___x_232_; 
lean_dec(v_h__2_227_);
v_val_230_ = lean_noption_get(v___key_224_);
v_val_231_ = lean_noption_get(v_value_225_);
v___x_232_ = lean_apply_2(v_h__1_226_, v_val_230_, v_val_231_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; 
lean_dec(v_h__1_226_);
v___x_233_ = lean_apply_3(v_h__2_227_, v___key_224_, v_value_225_, lean_box(0));
return v___x_233_;
}
}
else
{
lean_object* v___x_234_; 
lean_dec(v_h__1_226_);
v___x_234_ = lean_apply_3(v_h__2_227_, v___key_224_, v_value_225_, lean_box(0));
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_cellEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_motive_237_, lean_object* v___key_238_, lean_object* v_value_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_){
_start:
{
uint8_t v_isSome_242_; 
v_isSome_242_ = lean_noption_is_some(v___key_238_);
if (v_isSome_242_ == 1)
{
uint8_t v_isSome_243_; 
v_isSome_243_ = lean_noption_is_some(v_value_239_);
if (v_isSome_243_ == 1)
{
lean_object* v_val_244_; lean_object* v_val_245_; lean_object* v___x_246_; 
lean_dec(v_h__2_241_);
v_val_244_ = lean_noption_get(v___key_238_);
v_val_245_ = lean_noption_get(v_value_239_);
v___x_246_ = lean_apply_2(v_h__1_240_, v_val_244_, v_val_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
lean_dec(v_h__1_240_);
v___x_247_ = lean_apply_3(v_h__2_241_, v___key_238_, v_value_239_, lean_box(0));
return v___x_247_;
}
}
else
{
lean_object* v___x_248_; 
lean_dec(v_h__1_240_);
v___x_248_ = lean_apply_3(v_h__2_241_, v___key_238_, v_value_239_, lean_box(0));
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_entry_x3f_match__1_splitter___redArg(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_, lean_object* v_h__3_253_){
_start:
{
uint8_t v_isSome_254_; 
v_isSome_254_ = lean_noption_is_some(v_x_249_);
if (v_isSome_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_h__3_253_);
lean_dec(v_h__2_252_);
lean_dec(v_x_249_);
v___x_255_ = lean_apply_2(v_h__1_251_, v_x_250_, lean_box(0));
return v___x_255_;
}
else
{
lean_object* v_val_256_; uint8_t v_isSome_257_; 
lean_dec(v_h__1_251_);
v_val_256_ = lean_noption_get(v_x_249_);
v_isSome_257_ = lean_noption_is_some(v_x_250_);
if (v_isSome_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec(v_h__3_253_);
lean_dec(v_x_250_);
v___x_258_ = lean_apply_2(v_h__2_252_, v_val_256_, lean_box(0));
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_260_; 
lean_dec(v_h__2_252_);
v_val_259_ = lean_noption_get(v_x_250_);
v___x_260_ = lean_apply_3(v_h__3_253_, v_val_256_, v_val_259_, lean_box(0));
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_CellsMatch_entry_x3f_match__1_splitter(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_motive_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_, lean_object* v_h__3_269_){
_start:
{
uint8_t v_isSome_270_; 
v_isSome_270_ = lean_noption_is_some(v_x_264_);
if (v_isSome_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec(v_h__3_269_);
lean_dec(v_h__2_268_);
lean_dec(v_x_264_);
v___x_271_ = lean_apply_2(v_h__1_267_, v_x_265_, lean_box(0));
return v___x_271_;
}
else
{
lean_object* v_val_272_; uint8_t v_isSome_273_; 
lean_dec(v_h__1_267_);
v_val_272_ = lean_noption_get(v_x_264_);
v_isSome_273_ = lean_noption_is_some(v_x_265_);
if (v_isSome_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_h__3_269_);
lean_dec(v_x_265_);
v___x_274_ = lean_apply_2(v_h__2_268_, v_val_272_, lean_box(0));
return v___x_274_;
}
else
{
lean_object* v_val_275_; lean_object* v___x_276_; 
lean_dec(v_h__2_268_);
v_val_275_ = lean_noption_get(v_x_265_);
v___x_276_ = lean_apply_3(v_h__3_269_, v_val_272_, v_val_275_, lean_box(0));
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___redArg(lean_object* v_b_277_, lean_object* v_i_278_){
_start:
{
lean_object* v_keyArray_279_; lean_object* v_valueArray_280_; lean_object* v___x_281_; uint8_t v_isSome_282_; 
v_keyArray_279_ = lean_ctor_get(v_b_277_, 1);
v_valueArray_280_ = lean_ctor_get(v_b_277_, 2);
v___x_281_ = lean_array_fget_borrowed(v_keyArray_279_, v_i_278_);
v_isSome_282_ = lean_noption_is_some(v___x_281_);
if (v_isSome_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v___x_284_; uint8_t v_isSome_285_; 
v___x_284_ = lean_array_fget_borrowed(v_valueArray_280_, v_i_278_);
v_isSome_285_ = lean_noption_is_some(v___x_284_);
if (v_isSome_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
else
{
lean_object* v_val_287_; lean_object* v_val_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc(v___x_281_);
v_val_287_ = lean_noption_get(v___x_281_);
lean_inc(v___x_284_);
v_val_288_ = lean_noption_get(v___x_284_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_val_287_);
lean_ctor_set(v___x_289_, 1, v_val_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___redArg___boxed(lean_object* v_b_291_, lean_object* v_i_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___redArg(v_b_291_, v_i_292_);
lean_dec(v_i_292_);
lean_dec_ref(v_b_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f(lean_object* v_00_u03b1_294_, lean_object* v_00_u03b2_295_, lean_object* v_b_296_, lean_object* v_i_297_, lean_object* v_h_298_){
_start:
{
lean_object* v_keyArray_299_; lean_object* v_valueArray_300_; lean_object* v___x_301_; uint8_t v_isSome_302_; 
v_keyArray_299_ = lean_ctor_get(v_b_296_, 1);
v_valueArray_300_ = lean_ctor_get(v_b_296_, 2);
v___x_301_ = lean_array_fget_borrowed(v_keyArray_299_, v_i_297_);
v_isSome_302_ = lean_noption_is_some(v___x_301_);
if (v_isSome_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(0);
return v___x_303_;
}
else
{
lean_object* v___x_304_; uint8_t v_isSome_305_; 
v___x_304_ = lean_array_fget_borrowed(v_valueArray_300_, v_i_297_);
v_isSome_305_ = lean_noption_is_some(v___x_304_);
if (v_isSome_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_box(0);
return v___x_306_;
}
else
{
lean_object* v_val_307_; lean_object* v_val_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_inc(v___x_301_);
v_val_307_ = lean_noption_get(v___x_301_);
lean_inc(v___x_304_);
v_val_308_ = lean_noption_get(v___x_304_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_val_307_);
lean_ctor_set(v___x_309_, 1, v_val_308_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f___boxed(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_b_313_, lean_object* v_i_314_, lean_object* v_h_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_DHashMap_Raw_entryAtInBoundsImpl_x3f(v_00_u03b1_311_, v_00_u03b2_312_, v_b_313_, v_i_314_, v_h_315_);
lean_dec(v_i_314_);
lean_dec_ref(v_b_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f___redArg(lean_object* v_b_317_, lean_object* v_i_318_){
_start:
{
lean_object* v_keyArray_319_; lean_object* v_valueArray_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_keyArray_319_ = lean_ctor_get(v_b_317_, 1);
v_valueArray_320_ = lean_ctor_get(v_b_317_, 2);
v___x_321_ = lean_array_get_size(v_keyArray_319_);
v___x_322_ = lean_nat_dec_lt(v_i_318_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
else
{
lean_object* v___x_324_; uint8_t v_isSome_325_; 
v___x_324_ = lean_array_fget_borrowed(v_keyArray_319_, v_i_318_);
v_isSome_325_ = lean_noption_is_some(v___x_324_);
if (v_isSome_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v___x_327_; uint8_t v_isSome_328_; 
v___x_327_ = lean_array_fget_borrowed(v_valueArray_320_, v_i_318_);
v_isSome_328_ = lean_noption_is_some(v___x_327_);
if (v_isSome_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v_val_330_; lean_object* v_val_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_inc(v___x_324_);
v_val_330_ = lean_noption_get(v___x_324_);
lean_inc(v___x_327_);
v_val_331_ = lean_noption_get(v___x_327_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_val_330_);
lean_ctor_set(v___x_332_, 1, v_val_331_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f___redArg___boxed(lean_object* v_b_334_, lean_object* v_i_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_DHashMap_Raw_entryAt_x3f___redArg(v_b_334_, v_i_335_);
lean_dec(v_i_335_);
lean_dec_ref(v_b_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_b_339_, lean_object* v_i_340_){
_start:
{
lean_object* v_keyArray_341_; lean_object* v_valueArray_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_keyArray_341_ = lean_ctor_get(v_b_339_, 1);
v_valueArray_342_ = lean_ctor_get(v_b_339_, 2);
v___x_343_ = lean_array_get_size(v_keyArray_341_);
v___x_344_ = lean_nat_dec_lt(v_i_340_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
else
{
lean_object* v___x_346_; uint8_t v_isSome_347_; 
v___x_346_ = lean_array_fget_borrowed(v_keyArray_341_, v_i_340_);
v_isSome_347_ = lean_noption_is_some(v___x_346_);
if (v_isSome_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v___x_349_; uint8_t v_isSome_350_; 
v___x_349_ = lean_array_fget_borrowed(v_valueArray_342_, v_i_340_);
v_isSome_350_ = lean_noption_is_some(v___x_349_);
if (v_isSome_350_ == 0)
{
lean_object* v___x_351_; 
v___x_351_ = lean_box(0);
return v___x_351_;
}
else
{
lean_object* v_val_352_; lean_object* v_val_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_inc(v___x_346_);
v_val_352_ = lean_noption_get(v___x_346_);
lean_inc(v___x_349_);
v_val_353_ = lean_noption_get(v___x_349_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_val_352_);
lean_ctor_set(v___x_354_, 1, v_val_353_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entryAt_x3f___boxed(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_b_358_, lean_object* v_i_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_DHashMap_Raw_entryAt_x3f(v_00_u03b1_356_, v_00_u03b2_357_, v_b_358_, v_i_359_);
lean_dec(v_i_359_);
lean_dec_ref(v_b_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom___redArg(lean_object* v_b_361_, lean_object* v_i_362_){
_start:
{
lean_object* v_keyArray_367_; lean_object* v_valueArray_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_keyArray_367_ = lean_ctor_get(v_b_361_, 1);
v_valueArray_368_ = lean_ctor_get(v_b_361_, 2);
v___x_369_ = lean_array_get_size(v_keyArray_367_);
v___x_370_ = lean_nat_dec_lt(v_i_362_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_i_362_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v_isSome_373_; 
v___x_372_ = lean_array_fget_borrowed(v_keyArray_367_, v_i_362_);
v_isSome_373_ = lean_noption_is_some(v___x_372_);
if (v_isSome_373_ == 0)
{
goto v___jp_363_;
}
else
{
lean_object* v___x_374_; uint8_t v_isSome_375_; 
v___x_374_ = lean_array_fget_borrowed(v_valueArray_368_, v_i_362_);
v_isSome_375_ = lean_noption_is_some(v___x_374_);
if (v_isSome_375_ == 0)
{
goto v___jp_363_;
}
else
{
lean_object* v_val_376_; lean_object* v_val_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_inc(v___x_372_);
v_val_376_ = lean_noption_get(v___x_372_);
lean_inc(v___x_374_);
v_val_377_ = lean_noption_get(v___x_374_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_i_362_, v___x_378_);
lean_dec(v_i_362_);
v___x_380_ = l_Std_DHashMap_Raw_entriesFrom___redArg(v_b_361_, v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v_val_376_);
lean_ctor_set(v___x_381_, 1, v_val_377_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
return v___x_381_;
}
}
}
v___jp_363_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_add(v_i_362_, v___x_364_);
lean_dec(v_i_362_);
v_i_362_ = v___x_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom___redArg___boxed(lean_object* v_b_382_, lean_object* v_i_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_DHashMap_Raw_entriesFrom___redArg(v_b_382_, v_i_383_);
lean_dec_ref(v_b_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_b_387_, lean_object* v_i_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DHashMap_Raw_entriesFrom___redArg(v_b_387_, v_i_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_entriesFrom___boxed(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_b_392_, lean_object* v_i_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_DHashMap_Raw_entriesFrom(v_00_u03b1_390_, v_00_u03b2_391_, v_b_392_, v_i_393_);
lean_dec_ref(v_b_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_entriesFrom_match__1_splitter___redArg(lean_object* v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_h__2_397_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_apply_1(v_h__1_396_, v___x_398_);
return v___x_399_;
}
else
{
lean_object* v_val_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_403_; 
lean_dec(v_h__1_396_);
v_val_400_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_x_395_, 1);
v_fst_401_ = lean_ctor_get(v_val_400_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v_val_400_, 1);
lean_inc(v_snd_402_);
lean_dec(v_val_400_);
v___x_403_ = lean_apply_2(v_h__2_397_, v_fst_401_, v_snd_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_entriesFrom_match__1_splitter(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_motive_406_, lean_object* v_x_407_, lean_object* v_h__1_408_, lean_object* v_h__2_409_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_h__2_409_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_apply_1(v_h__1_408_, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_val_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_415_; 
lean_dec(v_h__1_408_);
v_val_412_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v_x_407_, 1);
v_fst_413_ = lean_ctor_get(v_val_412_, 0);
lean_inc(v_fst_413_);
v_snd_414_ = lean_ctor_get(v_val_412_, 1);
lean_inc(v_snd_414_);
lean_dec(v_val_412_);
v___x_415_ = lean_apply_2(v_h__2_409_, v_fst_413_, v_snd_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets___redArg(lean_object* v_b_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Std_DHashMap_Raw_entriesFrom___redArg(v_b_416_, v___x_417_);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_mk_empty_array_with_capacity(v___x_419_);
v___x_421_ = lean_array_push(v___x_420_, v___x_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets___redArg___boxed(lean_object* v_b_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_DHashMap_Raw_buckets___redArg(v_b_422_);
lean_dec_ref(v_b_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_b_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DHashMap_Raw_buckets___redArg(v_b_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_buckets___boxed(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_b_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Raw_buckets(v_00_u03b1_428_, v_00_u03b2_429_, v_b_430_);
lean_dec_ref(v_b_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___redArg___lam__0___boxed(lean_object* v_i_432_, lean_object* v_inst_433_, lean_object* v_f_434_, lean_object* v_b_435_, lean_object* v_____do__lift_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_DHashMap_Raw_foldMFrom___redArg___lam__0(v_i_432_, v_inst_433_, v_f_434_, v_b_435_, v_____do__lift_436_);
lean_dec(v_i_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___redArg(lean_object* v_inst_438_, lean_object* v_f_439_, lean_object* v_b_440_, lean_object* v_acc_441_, lean_object* v_i_442_){
_start:
{
lean_object* v_keyArray_447_; lean_object* v_valueArray_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_keyArray_447_ = lean_ctor_get(v_b_440_, 1);
v_valueArray_448_ = lean_ctor_get(v_b_440_, 2);
v___x_449_ = lean_array_get_size(v_keyArray_447_);
v___x_450_ = lean_nat_dec_lt(v_i_442_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v_toApplicative_451_; lean_object* v_toPure_452_; lean_object* v___x_453_; 
lean_dec(v_i_442_);
lean_dec_ref(v_b_440_);
lean_dec(v_f_439_);
v_toApplicative_451_ = lean_ctor_get(v_inst_438_, 0);
lean_inc_ref(v_toApplicative_451_);
lean_dec_ref(v_inst_438_);
v_toPure_452_ = lean_ctor_get(v_toApplicative_451_, 1);
lean_inc(v_toPure_452_);
lean_dec_ref(v_toApplicative_451_);
v___x_453_ = lean_apply_2(v_toPure_452_, lean_box(0), v_acc_441_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; uint8_t v_isSome_455_; 
v___x_454_ = lean_array_fget_borrowed(v_keyArray_447_, v_i_442_);
v_isSome_455_ = lean_noption_is_some(v___x_454_);
if (v_isSome_455_ == 0)
{
goto v___jp_443_;
}
else
{
lean_object* v___x_456_; uint8_t v_isSome_457_; 
v___x_456_ = lean_array_fget_borrowed(v_valueArray_448_, v_i_442_);
v_isSome_457_ = lean_noption_is_some(v___x_456_);
if (v_isSome_457_ == 0)
{
goto v___jp_443_;
}
else
{
lean_object* v_toBind_458_; lean_object* v___f_459_; lean_object* v_val_460_; lean_object* v_val_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v___x_456_);
lean_inc(v___x_454_);
v_toBind_458_ = lean_ctor_get(v_inst_438_, 1);
lean_inc(v_toBind_458_);
lean_inc(v_f_439_);
v___f_459_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldMFrom___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_459_, 0, v_i_442_);
lean_closure_set(v___f_459_, 1, v_inst_438_);
lean_closure_set(v___f_459_, 2, v_f_439_);
lean_closure_set(v___f_459_, 3, v_b_440_);
v_val_460_ = lean_noption_get(v___x_454_);
v_val_461_ = lean_noption_get(v___x_456_);
v___x_462_ = lean_apply_3(v_f_439_, v_acc_441_, v_val_460_, v_val_461_);
v___x_463_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v___x_462_, v___f_459_);
return v___x_463_;
}
}
}
v___jp_443_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_i_442_, v___x_444_);
lean_dec(v_i_442_);
v_i_442_ = v___x_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___redArg___lam__0(lean_object* v_i_464_, lean_object* v_inst_465_, lean_object* v_f_466_, lean_object* v_b_467_, lean_object* v_____do__lift_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_i_464_, v___x_469_);
v___x_471_ = l_Std_DHashMap_Raw_foldMFrom___redArg(v_inst_465_, v_f_466_, v_b_467_, v_____do__lift_468_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_00_u03b4_474_, lean_object* v_m_475_, lean_object* v_inst_476_, lean_object* v_f_477_, lean_object* v_b_478_, lean_object* v_acc_479_, lean_object* v_i_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DHashMap_Raw_foldMFrom___redArg(v_inst_476_, v_f_477_, v_b_478_, v_acc_479_, v_i_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object* v_inst_482_, lean_object* v_f_483_, lean_object* v_init_484_, lean_object* v_b_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = l_Std_DHashMap_Raw_foldMFrom___redArg(v_inst_482_, v_f_483_, v_b_485_, v_init_484_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_00_u03b4_490_, lean_object* v_m_491_, lean_object* v_inst_492_, lean_object* v_f_493_, lean_object* v_init_494_, lean_object* v_b_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_492_, v_f_493_, v_init_494_, v_b_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg___lam__0(lean_object* v_f_497_, lean_object* v_val_498_, lean_object* v_val_499_, lean_object* v_____do__lift_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_3(v_f_497_, v_____do__lift_500_, v_val_498_, v_val_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object* v_inst_502_, lean_object* v_f_503_, lean_object* v_b_504_, lean_object* v_acc_505_, lean_object* v_i_506_){
_start:
{
lean_object* v_keyArray_511_; lean_object* v_valueArray_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_keyArray_511_ = lean_ctor_get(v_b_504_, 1);
v_valueArray_512_ = lean_ctor_get(v_b_504_, 2);
v___x_513_ = lean_array_get_size(v_keyArray_511_);
v___x_514_ = lean_nat_dec_lt(v_i_506_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v_toApplicative_515_; lean_object* v_toPure_516_; lean_object* v___x_517_; 
lean_dec(v_i_506_);
lean_dec(v_f_503_);
v_toApplicative_515_ = lean_ctor_get(v_inst_502_, 0);
lean_inc_ref(v_toApplicative_515_);
lean_dec_ref(v_inst_502_);
v_toPure_516_ = lean_ctor_get(v_toApplicative_515_, 1);
lean_inc(v_toPure_516_);
lean_dec_ref(v_toApplicative_515_);
v___x_517_ = lean_apply_2(v_toPure_516_, lean_box(0), v_acc_505_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; uint8_t v_isSome_519_; 
v___x_518_ = lean_array_fget_borrowed(v_keyArray_511_, v_i_506_);
v_isSome_519_ = lean_noption_is_some(v___x_518_);
if (v_isSome_519_ == 0)
{
goto v___jp_507_;
}
else
{
lean_object* v___x_520_; uint8_t v_isSome_521_; 
v___x_520_ = lean_array_fget_borrowed(v_valueArray_512_, v_i_506_);
v_isSome_521_ = lean_noption_is_some(v___x_520_);
if (v_isSome_521_ == 0)
{
goto v___jp_507_;
}
else
{
lean_object* v_toBind_522_; lean_object* v_val_523_; lean_object* v_val_524_; lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_toBind_522_ = lean_ctor_get(v_inst_502_, 1);
lean_inc(v_toBind_522_);
lean_inc(v___x_518_);
v_val_523_ = lean_noption_get(v___x_518_);
lean_inc(v___x_520_);
v_val_524_ = lean_noption_get(v___x_520_);
lean_inc(v_f_503_);
v___f_525_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldRevMFrom___redArg___lam__0), 4, 3);
lean_closure_set(v___f_525_, 0, v_f_503_);
lean_closure_set(v___f_525_, 1, v_val_523_);
lean_closure_set(v___f_525_, 2, v_val_524_);
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_i_506_, v___x_526_);
lean_dec(v_i_506_);
v___x_528_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_502_, v_f_503_, v_b_504_, v_acc_505_, v___x_527_);
v___x_529_ = lean_apply_4(v_toBind_522_, lean_box(0), lean_box(0), v___x_528_, v___f_525_);
return v___x_529_;
}
}
}
v___jp_507_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_i_506_, v___x_508_);
lean_dec(v_i_506_);
v_i_506_ = v___x_509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg___boxed(lean_object* v_inst_530_, lean_object* v_f_531_, lean_object* v_b_532_, lean_object* v_acc_533_, lean_object* v_i_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_530_, v_f_531_, v_b_532_, v_acc_533_, v_i_534_);
lean_dec_ref(v_b_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_00_u03b4_538_, lean_object* v_m_539_, lean_object* v_inst_540_, lean_object* v_f_541_, lean_object* v_b_542_, lean_object* v_acc_543_, lean_object* v_i_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_540_, v_f_541_, v_b_542_, v_acc_543_, v_i_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_00_u03b4_548_, lean_object* v_m_549_, lean_object* v_inst_550_, lean_object* v_f_551_, lean_object* v_b_552_, lean_object* v_acc_553_, lean_object* v_i_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_DHashMap_Raw_foldRevMFrom(v_00_u03b1_546_, v_00_u03b2_547_, v_00_u03b4_548_, v_m_549_, v_inst_550_, v_f_551_, v_b_552_, v_acc_553_, v_i_554_);
lean_dec_ref(v_b_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__0(lean_object* v_f_556_, lean_object* v_x1_557_, lean_object* v_x2_558_, lean_object* v_x3_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_apply_3(v_f_556_, v_x1_557_, v_x2_558_, v_x3_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg(lean_object* v_f_580_, lean_object* v_init_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___f_583_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_583_, 0, v_f_580_);
v___x_584_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v___x_585_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_584_, v___f_583_, v_init_581_, v_b_582_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_00_u03b4_588_, lean_object* v_f_589_, lean_object* v_init_590_, lean_object* v_b_591_){
_start:
{
lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___f_592_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_592_, 0, v_f_589_);
v___x_593_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v___x_594_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_593_, v___f_592_, v_init_590_, v_b_591_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__0(lean_object* v_f_595_, lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_v_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_apply_2(v_f_595_, v_a_597_, v_v_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg(lean_object* v_inst_600_, lean_object* v_f_601_, lean_object* v_b_602_){
_start:
{
lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___f_603_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_603_, 0, v_f_601_);
v___x_604_ = lean_box(0);
v___x_605_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_600_, v___f_603_, v___x_604_, v_b_602_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM(lean_object* v_00_u03b1_606_, lean_object* v_00_u03b2_607_, lean_object* v_m_608_, lean_object* v_inst_609_, lean_object* v_f_610_, lean_object* v_b_611_){
_start:
{
lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___f_612_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_612_, 0, v_f_610_);
v___x_613_ = lean_box(0);
v___x_614_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_609_, v___f_612_, v___x_613_, v_b_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___redArg___lam__0___boxed(lean_object* v_toApplicative_615_, lean_object* v_i_616_, lean_object* v_inst_617_, lean_object* v_f_618_, lean_object* v_b_619_, lean_object* v_____do__lift_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Raw_forInFrom___redArg___lam__0(v_toApplicative_615_, v_i_616_, v_inst_617_, v_f_618_, v_b_619_, v_____do__lift_620_);
lean_dec(v_i_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___redArg(lean_object* v_inst_622_, lean_object* v_f_623_, lean_object* v_b_624_, lean_object* v_acc_625_, lean_object* v_i_626_){
_start:
{
lean_object* v_keyArray_631_; lean_object* v_valueArray_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_keyArray_631_ = lean_ctor_get(v_b_624_, 1);
v_valueArray_632_ = lean_ctor_get(v_b_624_, 2);
v___x_633_ = lean_array_get_size(v_keyArray_631_);
v___x_634_ = lean_nat_dec_lt(v_i_626_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v_toApplicative_635_; lean_object* v_toPure_636_; lean_object* v___x_637_; 
lean_dec(v_i_626_);
lean_dec_ref(v_b_624_);
lean_dec(v_f_623_);
v_toApplicative_635_ = lean_ctor_get(v_inst_622_, 0);
lean_inc_ref(v_toApplicative_635_);
lean_dec_ref(v_inst_622_);
v_toPure_636_ = lean_ctor_get(v_toApplicative_635_, 1);
lean_inc(v_toPure_636_);
lean_dec_ref(v_toApplicative_635_);
v___x_637_ = lean_apply_2(v_toPure_636_, lean_box(0), v_acc_625_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; uint8_t v_isSome_639_; 
v___x_638_ = lean_array_fget_borrowed(v_keyArray_631_, v_i_626_);
v_isSome_639_ = lean_noption_is_some(v___x_638_);
if (v_isSome_639_ == 0)
{
goto v___jp_627_;
}
else
{
lean_object* v___x_640_; uint8_t v_isSome_641_; 
v___x_640_ = lean_array_fget_borrowed(v_valueArray_632_, v_i_626_);
v_isSome_641_ = lean_noption_is_some(v___x_640_);
if (v_isSome_641_ == 0)
{
goto v___jp_627_;
}
else
{
lean_object* v_toApplicative_642_; lean_object* v_toBind_643_; lean_object* v___f_644_; lean_object* v_val_645_; lean_object* v_val_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
lean_inc(v___x_640_);
lean_inc(v___x_638_);
v_toApplicative_642_ = lean_ctor_get(v_inst_622_, 0);
lean_inc_ref(v_toApplicative_642_);
v_toBind_643_ = lean_ctor_get(v_inst_622_, 1);
lean_inc(v_toBind_643_);
lean_inc(v_f_623_);
v___f_644_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forInFrom___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_644_, 0, v_toApplicative_642_);
lean_closure_set(v___f_644_, 1, v_i_626_);
lean_closure_set(v___f_644_, 2, v_inst_622_);
lean_closure_set(v___f_644_, 3, v_f_623_);
lean_closure_set(v___f_644_, 4, v_b_624_);
v_val_645_ = lean_noption_get(v___x_638_);
v_val_646_ = lean_noption_get(v___x_640_);
v___x_647_ = lean_apply_3(v_f_623_, v_val_645_, v_val_646_, v_acc_625_);
v___x_648_ = lean_apply_4(v_toBind_643_, lean_box(0), lean_box(0), v___x_647_, v___f_644_);
return v___x_648_;
}
}
}
v___jp_627_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_i_626_, v___x_628_);
lean_dec(v_i_626_);
v_i_626_ = v___x_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___redArg___lam__0(lean_object* v_toApplicative_649_, lean_object* v_i_650_, lean_object* v_inst_651_, lean_object* v_f_652_, lean_object* v_b_653_, lean_object* v_____do__lift_654_){
_start:
{
if (lean_obj_tag(v_____do__lift_654_) == 0)
{
lean_object* v_a_655_; lean_object* v_toPure_656_; lean_object* v___x_657_; 
lean_dec_ref(v_b_653_);
lean_dec(v_f_652_);
lean_dec_ref(v_inst_651_);
v_a_655_ = lean_ctor_get(v_____do__lift_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v_____do__lift_654_, 1);
v_toPure_656_ = lean_ctor_get(v_toApplicative_649_, 1);
lean_inc(v_toPure_656_);
lean_dec_ref(v_toApplicative_649_);
v___x_657_ = lean_apply_2(v_toPure_656_, lean_box(0), v_a_655_);
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref(v_toApplicative_649_);
v_a_658_ = lean_ctor_get(v_____do__lift_654_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_____do__lift_654_, 1);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_i_650_, v___x_659_);
v___x_661_ = l_Std_DHashMap_Raw_forInFrom___redArg(v_inst_651_, v_f_652_, v_b_653_, v_a_658_, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_00_u03b4_664_, lean_object* v_m_665_, lean_object* v_inst_666_, lean_object* v_f_667_, lean_object* v_b_668_, lean_object* v_acc_669_, lean_object* v_i_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DHashMap_Raw_forInFrom___redArg(v_inst_666_, v_f_667_, v_b_668_, v_acc_669_, v_i_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_forInFrom_match__1_splitter___redArg(lean_object* v_____do__lift_672_, lean_object* v_h__1_673_, lean_object* v_h__2_674_){
_start:
{
if (lean_obj_tag(v_____do__lift_672_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
lean_dec(v_h__2_674_);
v_a_675_ = lean_ctor_get(v_____do__lift_672_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v_____do__lift_672_, 1);
v___x_676_ = lean_apply_1(v_h__1_673_, v_a_675_);
return v___x_676_;
}
else
{
lean_object* v_a_677_; lean_object* v___x_678_; 
lean_dec(v_h__1_673_);
v_a_677_ = lean_ctor_get(v_____do__lift_672_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v_____do__lift_672_, 1);
v___x_678_ = lean_apply_1(v_h__2_674_, v_a_677_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_RawDef_0__Std_DHashMap_Raw_forInFrom_match__1_splitter(lean_object* v_00_u03b4_679_, lean_object* v_motive_680_, lean_object* v_____do__lift_681_, lean_object* v_h__1_682_, lean_object* v_h__2_683_){
_start:
{
if (lean_obj_tag(v_____do__lift_681_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; 
lean_dec(v_h__2_683_);
v_a_684_ = lean_ctor_get(v_____do__lift_681_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v_____do__lift_681_, 1);
v___x_685_ = lean_apply_1(v_h__1_682_, v_a_684_);
return v___x_685_;
}
else
{
lean_object* v_a_686_; lean_object* v___x_687_; 
lean_dec(v_h__1_682_);
v_a_686_ = lean_ctor_get(v_____do__lift_681_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v_____do__lift_681_, 1);
v___x_687_ = lean_apply_1(v_h__2_683_, v_a_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object* v_inst_688_, lean_object* v_f_689_, lean_object* v_init_690_, lean_object* v_b_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Std_DHashMap_Raw_forInFrom___redArg(v_inst_688_, v_f_689_, v_b_691_, v_init_690_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_00_u03b4_696_, lean_object* v_m_697_, lean_object* v_inst_698_, lean_object* v_f_699_, lean_object* v_init_700_, lean_object* v_b_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_698_, v_f_699_, v_init_700_, v_b_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_703_, lean_object* v_x_704_, lean_object* v_a_705_, lean_object* v_v_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_a_705_);
lean_ctor_set(v___x_707_, 1, v_v_706_);
v___x_708_ = lean_apply_1(v_f_703_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_709_, lean_object* v_m_710_, lean_object* v_f_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___f_712_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_712_, 0, v_f_711_);
v___x_713_ = lean_box(0);
v___x_714_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_709_, v___f_712_, v___x_713_, v_m_710_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_715_){
_start:
{
lean_object* v___f_716_; 
v___f_716_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_716_, 0, v_inst_715_);
return v___f_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_m_719_, lean_object* v_inst_720_){
_start:
{
lean_object* v___f_721_; 
v___f_721_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_721_, 0, v_inst_720_);
return v___f_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_722_, lean_object* v_a_723_, lean_object* v_b_724_, lean_object* v_acc_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_a_723_);
lean_ctor_set(v___x_726_, 1, v_b_724_);
v___x_727_ = lean_apply_2(v_f_722_, v___x_726_, v_acc_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object* v_inst_728_, lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_init_731_, lean_object* v_f_732_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_734_; 
v___f_733_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_733_, 0, v_f_732_);
v___x_734_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_728_, v___f_733_, v_init_731_, v_m_730_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_735_){
_start:
{
lean_object* v___f_736_; 
v___f_736_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_736_, 0, v_inst_735_);
return v___f_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_m_739_, lean_object* v_inst_740_){
_start:
{
lean_object* v___f_741_; 
v___f_741_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_741_, 0, v_inst_740_);
return v___f_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0(lean_object* v_p_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v_a_745_, lean_object* v_b_746_, lean_object* v_acc_747_){
_start:
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_apply_2(v_p_742_, v_a_745_, v_b_746_);
v___x_749_ = lean_unbox(v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref(v___x_744_);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_743_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_744_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_754_, lean_object* v___x_755_, lean_object* v___x_756_, lean_object* v_a_757_, lean_object* v_b_758_, lean_object* v_acc_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DHashMap_Raw_all___redArg___lam__0(v_p_754_, v___x_755_, v___x_756_, v_a_757_, v_b_758_, v_acc_759_);
lean_dec_ref(v_acc_759_);
return v_res_760_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all___redArg(lean_object* v_m_764_, lean_object* v_p_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v_fst_771_; 
v___x_766_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v___x_767_ = lean_box(0);
v___x_768_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_769_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_769_, 0, v_p_765_);
lean_closure_set(v___f_769_, 1, v___x_767_);
lean_closure_set(v___f_769_, 2, v___x_768_);
v___x_770_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_766_, v___f_769_, v___x_768_, v_m_764_);
v_fst_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_fst_771_);
lean_dec(v___x_770_);
if (lean_obj_tag(v_fst_771_) == 0)
{
uint8_t v___x_772_; 
v___x_772_ = 1;
return v___x_772_;
}
else
{
lean_object* v_val_773_; uint8_t v___x_774_; 
v_val_773_ = lean_ctor_get(v_fst_771_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_fst_771_, 1);
v___x_774_ = lean_unbox(v_val_773_);
lean_dec(v_val_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___boxed(lean_object* v_m_775_, lean_object* v_p_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_Std_DHashMap_Raw_all___redArg(v_m_775_, v_p_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_m_781_, lean_object* v_p_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v_fst_788_; 
v___x_783_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v___x_784_ = lean_box(0);
v___x_785_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_786_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_786_, 0, v_p_782_);
lean_closure_set(v___f_786_, 1, v___x_784_);
lean_closure_set(v___f_786_, 2, v___x_785_);
v___x_787_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_783_, v___f_786_, v___x_785_, v_m_781_);
v_fst_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_fst_788_);
lean_dec(v___x_787_);
if (lean_obj_tag(v_fst_788_) == 0)
{
uint8_t v___x_789_; 
v___x_789_ = 1;
return v___x_789_;
}
else
{
lean_object* v_val_790_; uint8_t v___x_791_; 
v_val_790_ = lean_ctor_get(v_fst_788_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_fst_788_, 1);
v___x_791_ = lean_unbox(v_val_790_);
lean_dec(v_val_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___boxed(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_p_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Std_DHashMap_Raw_all(v_00_u03b1_792_, v_00_u03b2_793_, v_m_794_, v_p_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0(lean_object* v_p_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_b_802_, lean_object* v_acc_803_){
_start:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_apply_2(v_p_798_, v_a_801_, v_b_802_);
v___x_805_ = lean_unbox(v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_799_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v___x_799_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_800_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v_a_813_, lean_object* v_b_814_, lean_object* v_acc_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DHashMap_Raw_any___redArg___lam__0(v_p_810_, v___x_811_, v___x_812_, v_a_813_, v_b_814_, v_acc_815_);
lean_dec_ref(v_acc_815_);
return v_res_816_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any___redArg(lean_object* v_m_817_, lean_object* v_p_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v_fst_824_; 
v___x_819_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v___x_820_ = lean_box(0);
v___x_821_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_822_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_822_, 0, v_p_818_);
lean_closure_set(v___f_822_, 1, v___x_821_);
lean_closure_set(v___f_822_, 2, v___x_820_);
v___x_823_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_819_, v___f_822_, v___x_821_, v_m_817_);
v_fst_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_fst_824_);
lean_dec(v___x_823_);
if (lean_obj_tag(v_fst_824_) == 0)
{
uint8_t v___x_825_; 
v___x_825_ = 0;
return v___x_825_;
}
else
{
lean_object* v_val_826_; uint8_t v___x_827_; 
v_val_826_ = lean_ctor_get(v_fst_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_fst_824_, 1);
v___x_827_ = lean_unbox(v_val_826_);
lean_dec(v_val_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___boxed(lean_object* v_m_828_, lean_object* v_p_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_DHashMap_Raw_any___redArg(v_m_828_, v_p_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_m_834_, lean_object* v_p_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v_fst_841_; 
v___x_836_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v___x_837_ = lean_box(0);
v___x_838_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_839_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_839_, 0, v_p_835_);
lean_closure_set(v___f_839_, 1, v___x_838_);
lean_closure_set(v___f_839_, 2, v___x_837_);
v___x_840_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_836_, v___f_839_, v___x_838_, v_m_834_);
v_fst_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_fst_841_);
lean_dec(v___x_840_);
if (lean_obj_tag(v_fst_841_) == 0)
{
uint8_t v___x_842_; 
v___x_842_ = 0;
return v___x_842_;
}
else
{
lean_object* v_val_843_; uint8_t v___x_844_; 
v_val_843_ = lean_ctor_get(v_fst_841_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v_fst_841_, 1);
v___x_844_ = lean_unbox(v_val_843_);
lean_dec(v_val_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___boxed(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_m_847_, lean_object* v_p_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Std_DHashMap_Raw_any(v_00_u03b1_845_, v_00_u03b2_846_, v_m_847_, v_p_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Erased(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Fold(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Erased(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Erased(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Fold(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Erased(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_RawDef(builtin);
}
#ifdef __cplusplus
}
#endif
