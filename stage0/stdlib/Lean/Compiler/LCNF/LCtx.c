// Lean compiler output
// Module: Lean.Compiler.LCNF.LCtx
// Imports: public import Lean.Compiler.LCNF.Basic
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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1);
v___x_8_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
lean_ctor_set(v___x_8_, 2, v___x_7_);
lean_ctor_set(v___x_8_, 3, v___x_7_);
lean_ctor_set(v___x_8_, 4, v___x_7_);
lean_ctor_set(v___x_8_, 5, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
return v___x_10_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
else
{
lean_object* v_key_14_; lean_object* v_tail_15_; uint8_t v___x_16_; 
v_key_14_ = lean_ctor_get(v_x_12_, 0);
v_tail_15_ = lean_ctor_get(v_x_12_, 2);
v___x_16_ = l_Lean_instBEqFVarId_beq(v_key_14_, v_a_11_);
if (v___x_16_ == 0)
{
v_x_12_ = v_tail_15_;
goto _start;
}
else
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg___boxed(lean_object* v_a_18_, lean_object* v_x_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_18_, v_x_19_);
lean_dec(v_x_19_);
lean_dec(v_a_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
return v_x_22_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_49_; 
v_key_24_ = lean_ctor_get(v_x_23_, 0);
v_value_25_ = lean_ctor_get(v_x_23_, 1);
v_tail_26_ = lean_ctor_get(v_x_23_, 2);
v_isSharedCheck_49_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_49_ == 0)
{
v___x_28_ = v_x_23_;
v_isShared_29_ = v_isSharedCheck_49_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_value_25_);
lean_inc(v_key_24_);
lean_dec(v_x_23_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_49_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v_fold_34_; uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; size_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_30_ = lean_array_get_size(v_x_22_);
v___x_31_ = l_Lean_instHashableFVarId_hash(v_key_24_);
v___x_32_ = 32ULL;
v___x_33_ = lean_uint64_shift_right(v___x_31_, v___x_32_);
v_fold_34_ = lean_uint64_xor(v___x_31_, v___x_33_);
v___x_35_ = 16ULL;
v___x_36_ = lean_uint64_shift_right(v_fold_34_, v___x_35_);
v___x_37_ = lean_uint64_xor(v_fold_34_, v___x_36_);
v___x_38_ = lean_uint64_to_usize(v___x_37_);
v___x_39_ = lean_usize_of_nat(v___x_30_);
v___x_40_ = ((size_t)1ULL);
v___x_41_ = lean_usize_sub(v___x_39_, v___x_40_);
v___x_42_ = lean_usize_land(v___x_38_, v___x_41_);
v___x_43_ = lean_array_uget_borrowed(v_x_22_, v___x_42_);
lean_inc(v___x_43_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 2, v___x_43_);
v___x_45_ = v___x_28_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_key_24_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_value_25_);
lean_ctor_set(v_reuseFailAlloc_48_, 2, v___x_43_);
v___x_45_ = v_reuseFailAlloc_48_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; 
v___x_46_ = lean_array_uset(v_x_22_, v___x_42_, v___x_45_);
v_x_22_ = v___x_46_;
v_x_23_ = v_tail_26_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(lean_object* v_i_50_, lean_object* v_source_51_, lean_object* v_target_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_array_get_size(v_source_51_);
v___x_54_ = lean_nat_dec_lt(v_i_50_, v___x_53_);
if (v___x_54_ == 0)
{
lean_dec_ref(v_source_51_);
lean_dec(v_i_50_);
return v_target_52_;
}
else
{
lean_object* v_es_55_; lean_object* v___x_56_; lean_object* v_source_57_; lean_object* v_target_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_es_55_ = lean_array_fget(v_source_51_, v_i_50_);
v___x_56_ = lean_box(0);
v_source_57_ = lean_array_fset(v_source_51_, v_i_50_, v___x_56_);
v_target_58_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_target_52_, v_es_55_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_i_50_, v___x_59_);
lean_dec(v_i_50_);
v_i_50_ = v___x_60_;
v_source_51_ = v_source_57_;
v_target_52_ = v_target_58_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(lean_object* v_data_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_nbuckets_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_63_ = lean_array_get_size(v_data_62_);
v___x_64_ = lean_unsigned_to_nat(2u);
v_nbuckets_65_ = lean_nat_mul(v___x_63_, v___x_64_);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_box(0);
v___x_68_ = lean_mk_array(v_nbuckets_65_, v___x_67_);
v___x_69_ = lean_array_propagate_mark(v_data_62_, v___x_68_);
v___x_70_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v___x_66_, v_data_62_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(lean_object* v_a_71_, lean_object* v_b_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_dec(v_b_72_);
lean_dec(v_a_71_);
return v_x_73_;
}
else
{
lean_object* v_key_74_; lean_object* v_value_75_; lean_object* v_tail_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_88_; 
v_key_74_ = lean_ctor_get(v_x_73_, 0);
v_value_75_ = lean_ctor_get(v_x_73_, 1);
v_tail_76_ = lean_ctor_get(v_x_73_, 2);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_88_ == 0)
{
v___x_78_ = v_x_73_;
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_tail_76_);
lean_inc(v_value_75_);
lean_inc(v_key_74_);
lean_dec(v_x_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; 
v___x_80_ = l_Lean_instBEqFVarId_beq(v_key_74_, v_a_71_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_71_, v_b_72_, v_tail_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 2, v___x_81_);
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_key_74_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_value_75_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v_value_75_);
lean_dec(v_key_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v_b_72_);
lean_ctor_set(v___x_78_, 0, v_a_71_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_71_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_b_72_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_tail_76_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object* v_m_89_, lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_size_92_; lean_object* v_buckets_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_136_; 
v_size_92_ = lean_ctor_get(v_m_89_, 0);
v_buckets_93_ = lean_ctor_get(v_m_89_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_m_89_);
if (v_isSharedCheck_136_ == 0)
{
v___x_95_ = v_m_89_;
v_isShared_96_ = v_isSharedCheck_136_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_buckets_93_);
lean_inc(v_size_92_);
lean_dec(v_m_89_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_136_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v_fold_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; lean_object* v_bkt_110_; uint8_t v___x_111_; 
v___x_97_ = lean_array_get_size(v_buckets_93_);
v___x_98_ = l_Lean_instHashableFVarId_hash(v_a_90_);
v___x_99_ = 32ULL;
v___x_100_ = lean_uint64_shift_right(v___x_98_, v___x_99_);
v_fold_101_ = lean_uint64_xor(v___x_98_, v___x_100_);
v___x_102_ = 16ULL;
v___x_103_ = lean_uint64_shift_right(v_fold_101_, v___x_102_);
v___x_104_ = lean_uint64_xor(v_fold_101_, v___x_103_);
v___x_105_ = lean_uint64_to_usize(v___x_104_);
v___x_106_ = lean_usize_of_nat(v___x_97_);
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_sub(v___x_106_, v___x_107_);
v___x_109_ = lean_usize_land(v___x_105_, v___x_108_);
v_bkt_110_ = lean_array_uget_borrowed(v_buckets_93_, v___x_109_);
v___x_111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_90_, v_bkt_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v_size_x27_113_; lean_object* v___x_114_; lean_object* v_buckets_x27_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v_size_x27_113_ = lean_nat_add(v_size_92_, v___x_112_);
lean_dec(v_size_92_);
lean_inc(v_bkt_110_);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v_a_90_);
lean_ctor_set(v___x_114_, 1, v_b_91_);
lean_ctor_set(v___x_114_, 2, v_bkt_110_);
v_buckets_x27_115_ = lean_array_uset(v_buckets_93_, v___x_109_, v___x_114_);
v___x_116_ = lean_unsigned_to_nat(4u);
v___x_117_ = lean_nat_mul(v_size_x27_113_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(3u);
v___x_119_ = lean_nat_div(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_array_get_size(v_buckets_x27_115_);
v___x_121_ = lean_nat_dec_le(v___x_119_, v___x_120_);
lean_dec(v___x_119_);
if (v___x_121_ == 0)
{
lean_object* v_val_122_; lean_object* v___x_124_; 
v_val_122_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_buckets_x27_115_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v_val_122_);
lean_ctor_set(v___x_95_, 0, v_size_x27_113_);
v___x_124_ = v___x_95_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_size_x27_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_val_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_127_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v_buckets_x27_115_);
lean_ctor_set(v___x_95_, 0, v_size_x27_113_);
v___x_127_ = v___x_95_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_size_x27_113_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_buckets_x27_115_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v___x_129_; lean_object* v_buckets_x27_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc(v_bkt_110_);
v___x_129_ = lean_box(0);
v_buckets_x27_130_ = lean_array_uset(v_buckets_93_, v___x_109_, v___x_129_);
v___x_131_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_90_, v_b_91_, v_bkt_110_);
v___x_132_ = lean_array_uset(v_buckets_x27_130_, v___x_109_, v___x_131_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v___x_132_);
v___x_134_ = v___x_95_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_size_92_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t v_pu_137_, lean_object* v_lctx_138_, lean_object* v_param_139_){
_start:
{
if (v_pu_137_ == 0)
{
lean_object* v_paramsPure_140_; lean_object* v_paramsImpure_141_; lean_object* v_letDeclsPure_142_; lean_object* v_letDeclsImpure_143_; lean_object* v_funDeclsPure_144_; lean_object* v_funDeclsImpure_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
v_paramsPure_140_ = lean_ctor_get(v_lctx_138_, 0);
v_paramsImpure_141_ = lean_ctor_get(v_lctx_138_, 1);
v_letDeclsPure_142_ = lean_ctor_get(v_lctx_138_, 2);
v_letDeclsImpure_143_ = lean_ctor_get(v_lctx_138_, 3);
v_funDeclsPure_144_ = lean_ctor_get(v_lctx_138_, 4);
v_funDeclsImpure_145_ = lean_ctor_get(v_lctx_138_, 5);
v_isSharedCheck_154_ = !lean_is_exclusive(v_lctx_138_);
if (v_isSharedCheck_154_ == 0)
{
v___x_147_ = v_lctx_138_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_funDeclsImpure_145_);
lean_inc(v_funDeclsPure_144_);
lean_inc(v_letDeclsImpure_143_);
lean_inc(v_letDeclsPure_142_);
lean_inc(v_paramsImpure_141_);
lean_inc(v_paramsPure_140_);
lean_dec(v_lctx_138_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_fvarId_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v_fvarId_149_ = lean_ctor_get(v_param_139_, 0);
lean_inc(v_fvarId_149_);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsPure_140_, v_fvarId_149_, v_param_139_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_paramsImpure_141_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_letDeclsPure_142_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v_letDeclsImpure_143_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v_funDeclsPure_144_);
lean_ctor_set(v_reuseFailAlloc_153_, 5, v_funDeclsImpure_145_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v_paramsPure_155_; lean_object* v_paramsImpure_156_; lean_object* v_letDeclsPure_157_; lean_object* v_letDeclsImpure_158_; lean_object* v_funDeclsPure_159_; lean_object* v_funDeclsImpure_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_169_; 
v_paramsPure_155_ = lean_ctor_get(v_lctx_138_, 0);
v_paramsImpure_156_ = lean_ctor_get(v_lctx_138_, 1);
v_letDeclsPure_157_ = lean_ctor_get(v_lctx_138_, 2);
v_letDeclsImpure_158_ = lean_ctor_get(v_lctx_138_, 3);
v_funDeclsPure_159_ = lean_ctor_get(v_lctx_138_, 4);
v_funDeclsImpure_160_ = lean_ctor_get(v_lctx_138_, 5);
v_isSharedCheck_169_ = !lean_is_exclusive(v_lctx_138_);
if (v_isSharedCheck_169_ == 0)
{
v___x_162_ = v_lctx_138_;
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_funDeclsImpure_160_);
lean_inc(v_funDeclsPure_159_);
lean_inc(v_letDeclsImpure_158_);
lean_inc(v_letDeclsPure_157_);
lean_inc(v_paramsImpure_156_);
lean_inc(v_paramsPure_155_);
lean_dec(v_lctx_138_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_fvarId_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v_fvarId_164_ = lean_ctor_get(v_param_139_, 0);
lean_inc(v_fvarId_164_);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsImpure_156_, v_fvarId_164_, v_param_139_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v___x_165_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_paramsPure_155_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_letDeclsPure_157_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_letDeclsImpure_158_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_funDeclsPure_159_);
lean_ctor_set(v_reuseFailAlloc_168_, 5, v_funDeclsImpure_160_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam___boxed(lean_object* v_pu_170_, lean_object* v_lctx_171_, lean_object* v_param_172_){
_start:
{
uint8_t v_pu_boxed_173_; lean_object* v_res_174_; 
v_pu_boxed_173_ = lean_unbox(v_pu_170_);
v_res_174_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_boxed_173_, v_lctx_171_, v_param_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object* v_00_u03b2_175_, lean_object* v_m_176_, lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_176_, v_a_177_, v_b_178_);
return v___x_179_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_object* v_00_u03b2_180_, lean_object* v_a_181_, lean_object* v_x_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_181_, v_x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_184_, lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(v_00_u03b2_184_, v_a_185_, v_x_186_);
lean_dec(v_x_186_);
lean_dec(v_a_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1(lean_object* v_00_u03b2_189_, lean_object* v_data_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_data_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2(lean_object* v_00_u03b2_192_, lean_object* v_a_193_, lean_object* v_b_194_, lean_object* v_x_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_193_, v_b_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_197_, lean_object* v_i_198_, lean_object* v_source_199_, lean_object* v_target_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v_i_198_, v_source_199_, v_target_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_x_203_, v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t v_pu_206_, lean_object* v_lctx_207_, lean_object* v_letDecl_208_){
_start:
{
if (v_pu_206_ == 0)
{
lean_object* v_paramsPure_209_; lean_object* v_paramsImpure_210_; lean_object* v_letDeclsPure_211_; lean_object* v_letDeclsImpure_212_; lean_object* v_funDeclsPure_213_; lean_object* v_funDeclsImpure_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
v_paramsPure_209_ = lean_ctor_get(v_lctx_207_, 0);
v_paramsImpure_210_ = lean_ctor_get(v_lctx_207_, 1);
v_letDeclsPure_211_ = lean_ctor_get(v_lctx_207_, 2);
v_letDeclsImpure_212_ = lean_ctor_get(v_lctx_207_, 3);
v_funDeclsPure_213_ = lean_ctor_get(v_lctx_207_, 4);
v_funDeclsImpure_214_ = lean_ctor_get(v_lctx_207_, 5);
v_isSharedCheck_223_ = !lean_is_exclusive(v_lctx_207_);
if (v_isSharedCheck_223_ == 0)
{
v___x_216_ = v_lctx_207_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_funDeclsImpure_214_);
lean_inc(v_funDeclsPure_213_);
lean_inc(v_letDeclsImpure_212_);
lean_inc(v_letDeclsPure_211_);
lean_inc(v_paramsImpure_210_);
lean_inc(v_paramsPure_209_);
lean_dec(v_lctx_207_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_fvarId_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v_fvarId_218_ = lean_ctor_get(v_letDecl_208_, 0);
lean_inc(v_fvarId_218_);
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsPure_211_, v_fvarId_218_, v_letDecl_208_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 2, v___x_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_paramsPure_209_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_paramsImpure_210_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_letDeclsImpure_212_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v_funDeclsPure_213_);
lean_ctor_set(v_reuseFailAlloc_222_, 5, v_funDeclsImpure_214_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_paramsPure_224_; lean_object* v_paramsImpure_225_; lean_object* v_letDeclsPure_226_; lean_object* v_letDeclsImpure_227_; lean_object* v_funDeclsPure_228_; lean_object* v_funDeclsImpure_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
v_paramsPure_224_ = lean_ctor_get(v_lctx_207_, 0);
v_paramsImpure_225_ = lean_ctor_get(v_lctx_207_, 1);
v_letDeclsPure_226_ = lean_ctor_get(v_lctx_207_, 2);
v_letDeclsImpure_227_ = lean_ctor_get(v_lctx_207_, 3);
v_funDeclsPure_228_ = lean_ctor_get(v_lctx_207_, 4);
v_funDeclsImpure_229_ = lean_ctor_get(v_lctx_207_, 5);
v_isSharedCheck_238_ = !lean_is_exclusive(v_lctx_207_);
if (v_isSharedCheck_238_ == 0)
{
v___x_231_ = v_lctx_207_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_funDeclsImpure_229_);
lean_inc(v_funDeclsPure_228_);
lean_inc(v_letDeclsImpure_227_);
lean_inc(v_letDeclsPure_226_);
lean_inc(v_paramsImpure_225_);
lean_inc(v_paramsPure_224_);
lean_dec(v_lctx_207_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_fvarId_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v_fvarId_233_ = lean_ctor_get(v_letDecl_208_, 0);
lean_inc(v_fvarId_233_);
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsImpure_227_, v_fvarId_233_, v_letDecl_208_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 3, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_paramsPure_224_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_paramsImpure_225_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_letDeclsPure_226_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_funDeclsPure_228_);
lean_ctor_set(v_reuseFailAlloc_237_, 5, v_funDeclsImpure_229_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(lean_object* v_pu_239_, lean_object* v_lctx_240_, lean_object* v_letDecl_241_){
_start:
{
uint8_t v_pu_boxed_242_; lean_object* v_res_243_; 
v_pu_boxed_242_ = lean_unbox(v_pu_239_);
v_res_243_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_boxed_242_, v_lctx_240_, v_letDecl_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t v_pu_244_, lean_object* v_lctx_245_, lean_object* v_funDecl_246_){
_start:
{
if (v_pu_244_ == 0)
{
lean_object* v_fvarId_247_; lean_object* v_paramsPure_248_; lean_object* v_paramsImpure_249_; lean_object* v_letDeclsPure_250_; lean_object* v_letDeclsImpure_251_; lean_object* v_funDeclsPure_252_; lean_object* v_funDeclsImpure_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_fvarId_247_ = lean_ctor_get(v_funDecl_246_, 0);
lean_inc(v_fvarId_247_);
v_paramsPure_248_ = lean_ctor_get(v_lctx_245_, 0);
v_paramsImpure_249_ = lean_ctor_get(v_lctx_245_, 1);
v_letDeclsPure_250_ = lean_ctor_get(v_lctx_245_, 2);
v_letDeclsImpure_251_ = lean_ctor_get(v_lctx_245_, 3);
v_funDeclsPure_252_ = lean_ctor_get(v_lctx_245_, 4);
v_funDeclsImpure_253_ = lean_ctor_get(v_lctx_245_, 5);
v_isSharedCheck_261_ = !lean_is_exclusive(v_lctx_245_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_lctx_245_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_funDeclsImpure_253_);
lean_inc(v_funDeclsPure_252_);
lean_inc(v_letDeclsImpure_251_);
lean_inc(v_letDeclsPure_250_);
lean_inc(v_paramsImpure_249_);
lean_inc(v_paramsPure_248_);
lean_dec(v_lctx_245_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsPure_252_, v_fvarId_247_, v_funDecl_246_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 4, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_paramsPure_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_paramsImpure_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_letDeclsPure_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_letDeclsImpure_251_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 5, v_funDeclsImpure_253_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_fvarId_262_; lean_object* v_paramsPure_263_; lean_object* v_paramsImpure_264_; lean_object* v_letDeclsPure_265_; lean_object* v_letDeclsImpure_266_; lean_object* v_funDeclsPure_267_; lean_object* v_funDeclsImpure_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_fvarId_262_ = lean_ctor_get(v_funDecl_246_, 0);
lean_inc(v_fvarId_262_);
v_paramsPure_263_ = lean_ctor_get(v_lctx_245_, 0);
v_paramsImpure_264_ = lean_ctor_get(v_lctx_245_, 1);
v_letDeclsPure_265_ = lean_ctor_get(v_lctx_245_, 2);
v_letDeclsImpure_266_ = lean_ctor_get(v_lctx_245_, 3);
v_funDeclsPure_267_ = lean_ctor_get(v_lctx_245_, 4);
v_funDeclsImpure_268_ = lean_ctor_get(v_lctx_245_, 5);
v_isSharedCheck_276_ = !lean_is_exclusive(v_lctx_245_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v_lctx_245_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_funDeclsImpure_268_);
lean_inc(v_funDeclsPure_267_);
lean_inc(v_letDeclsImpure_266_);
lean_inc(v_letDeclsPure_265_);
lean_inc(v_paramsImpure_264_);
lean_inc(v_paramsPure_263_);
lean_dec(v_lctx_245_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsImpure_268_, v_fvarId_262_, v_funDecl_246_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 5, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_paramsPure_263_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_paramsImpure_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_letDeclsPure_265_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_letDeclsImpure_266_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_funDeclsPure_267_);
lean_ctor_set(v_reuseFailAlloc_275_, 5, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(lean_object* v_pu_277_, lean_object* v_lctx_278_, lean_object* v_funDecl_279_){
_start:
{
uint8_t v_pu_boxed_280_; lean_object* v_res_281_; 
v_pu_boxed_280_ = lean_unbox(v_pu_277_);
v_res_281_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_boxed_280_, v_lctx_278_, v_funDecl_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
return v_x_283_;
}
else
{
lean_object* v_key_284_; lean_object* v_value_285_; lean_object* v_tail_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_295_; 
v_key_284_ = lean_ctor_get(v_x_283_, 0);
v_value_285_ = lean_ctor_get(v_x_283_, 1);
v_tail_286_ = lean_ctor_get(v_x_283_, 2);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_295_ == 0)
{
v___x_288_ = v_x_283_;
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_tail_286_);
lean_inc(v_value_285_);
lean_inc(v_key_284_);
lean_dec(v_x_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; 
v___x_290_ = l_Lean_instBEqFVarId_beq(v_key_284_, v_a_282_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_282_, v_tail_286_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 2, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_key_284_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_value_285_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
lean_del_object(v___x_288_);
lean_dec(v_value_285_);
lean_dec(v_key_284_);
return v_tail_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(lean_object* v_a_296_, lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_296_, v_x_297_);
lean_dec(v_a_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object* v_m_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_size_301_; lean_object* v_buckets_302_; lean_object* v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v_fold_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v_bkt_316_; uint8_t v___x_317_; 
v_size_301_ = lean_ctor_get(v_m_299_, 0);
v_buckets_302_ = lean_ctor_get(v_m_299_, 1);
v___x_303_ = lean_array_get_size(v_buckets_302_);
v___x_304_ = l_Lean_instHashableFVarId_hash(v_a_300_);
v___x_305_ = 32ULL;
v___x_306_ = lean_uint64_shift_right(v___x_304_, v___x_305_);
v_fold_307_ = lean_uint64_xor(v___x_304_, v___x_306_);
v___x_308_ = 16ULL;
v___x_309_ = lean_uint64_shift_right(v_fold_307_, v___x_308_);
v___x_310_ = lean_uint64_xor(v_fold_307_, v___x_309_);
v___x_311_ = lean_uint64_to_usize(v___x_310_);
v___x_312_ = lean_usize_of_nat(v___x_303_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_sub(v___x_312_, v___x_313_);
v___x_315_ = lean_usize_land(v___x_311_, v___x_314_);
v_bkt_316_ = lean_array_uget_borrowed(v_buckets_302_, v___x_315_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_300_, v_bkt_316_);
if (v___x_317_ == 0)
{
return v_m_299_;
}
else
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_330_; 
lean_inc(v_bkt_316_);
lean_inc_ref(v_buckets_302_);
lean_inc(v_size_301_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_m_299_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_331_ = lean_ctor_get(v_m_299_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_m_299_, 0);
lean_dec(v_unused_332_);
v___x_319_ = v_m_299_;
v_isShared_320_ = v_isSharedCheck_330_;
goto v_resetjp_318_;
}
else
{
lean_dec(v_m_299_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_330_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v_buckets_x27_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_321_ = lean_box(0);
v_buckets_x27_322_ = lean_array_uset(v_buckets_302_, v___x_315_, v___x_321_);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_sub(v_size_301_, v___x_323_);
lean_dec(v_size_301_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_300_, v_bkt_316_);
v___x_326_ = lean_array_uset(v_buckets_x27_322_, v___x_315_, v___x_325_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_326_);
lean_ctor_set(v___x_319_, 0, v___x_324_);
v___x_328_ = v___x_319_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(lean_object* v_m_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_333_, v_a_334_);
lean_dec(v_a_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t v_pu_336_, lean_object* v_lctx_337_, lean_object* v_param_338_){
_start:
{
if (v_pu_336_ == 0)
{
lean_object* v_paramsPure_339_; lean_object* v_paramsImpure_340_; lean_object* v_letDeclsPure_341_; lean_object* v_letDeclsImpure_342_; lean_object* v_funDeclsPure_343_; lean_object* v_funDeclsImpure_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_353_; 
v_paramsPure_339_ = lean_ctor_get(v_lctx_337_, 0);
v_paramsImpure_340_ = lean_ctor_get(v_lctx_337_, 1);
v_letDeclsPure_341_ = lean_ctor_get(v_lctx_337_, 2);
v_letDeclsImpure_342_ = lean_ctor_get(v_lctx_337_, 3);
v_funDeclsPure_343_ = lean_ctor_get(v_lctx_337_, 4);
v_funDeclsImpure_344_ = lean_ctor_get(v_lctx_337_, 5);
v_isSharedCheck_353_ = !lean_is_exclusive(v_lctx_337_);
if (v_isSharedCheck_353_ == 0)
{
v___x_346_ = v_lctx_337_;
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_funDeclsImpure_344_);
lean_inc(v_funDeclsPure_343_);
lean_inc(v_letDeclsImpure_342_);
lean_inc(v_letDeclsPure_341_);
lean_inc(v_paramsImpure_340_);
lean_inc(v_paramsPure_339_);
lean_dec(v_lctx_337_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_fvarId_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v_fvarId_348_ = lean_ctor_get(v_param_338_, 0);
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsPure_339_, v_fvarId_348_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_paramsImpure_340_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_letDeclsPure_341_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_letDeclsImpure_342_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_funDeclsPure_343_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v_funDeclsImpure_344_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
else
{
lean_object* v_paramsPure_354_; lean_object* v_paramsImpure_355_; lean_object* v_letDeclsPure_356_; lean_object* v_letDeclsImpure_357_; lean_object* v_funDeclsPure_358_; lean_object* v_funDeclsImpure_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v_paramsPure_354_ = lean_ctor_get(v_lctx_337_, 0);
v_paramsImpure_355_ = lean_ctor_get(v_lctx_337_, 1);
v_letDeclsPure_356_ = lean_ctor_get(v_lctx_337_, 2);
v_letDeclsImpure_357_ = lean_ctor_get(v_lctx_337_, 3);
v_funDeclsPure_358_ = lean_ctor_get(v_lctx_337_, 4);
v_funDeclsImpure_359_ = lean_ctor_get(v_lctx_337_, 5);
v_isSharedCheck_368_ = !lean_is_exclusive(v_lctx_337_);
if (v_isSharedCheck_368_ == 0)
{
v___x_361_ = v_lctx_337_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_funDeclsImpure_359_);
lean_inc(v_funDeclsPure_358_);
lean_inc(v_letDeclsImpure_357_);
lean_inc(v_letDeclsPure_356_);
lean_inc(v_paramsImpure_355_);
lean_inc(v_paramsPure_354_);
lean_dec(v_lctx_337_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_fvarId_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v_fvarId_363_ = lean_ctor_get(v_param_338_, 0);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsImpure_355_, v_fvarId_363_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_paramsPure_354_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_letDeclsPure_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_letDeclsImpure_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_funDeclsPure_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v_funDeclsImpure_359_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(lean_object* v_pu_369_, lean_object* v_lctx_370_, lean_object* v_param_371_){
_start:
{
uint8_t v_pu_boxed_372_; lean_object* v_res_373_; 
v_pu_boxed_372_ = lean_unbox(v_pu_369_);
v_res_373_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_boxed_372_, v_lctx_370_, v_param_371_);
lean_dec_ref(v_param_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(lean_object* v_00_u03b2_374_, lean_object* v_m_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_375_, v_a_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(lean_object* v_00_u03b2_378_, lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(v_00_u03b2_378_, v_m_379_, v_a_380_);
lean_dec(v_a_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(lean_object* v_00_u03b2_382_, lean_object* v_a_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_383_, v_x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_386_, lean_object* v_a_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(v_00_u03b2_386_, v_a_387_, v_x_388_);
lean_dec(v_a_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(lean_object* v_as_390_, size_t v_i_391_, size_t v_stop_392_, lean_object* v_b_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_391_, v_stop_392_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v_fvarId_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; 
v___x_395_ = lean_array_uget_borrowed(v_as_390_, v_i_391_);
v_fvarId_396_ = lean_ctor_get(v___x_395_, 0);
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_b_393_, v_fvarId_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_391_, v___x_398_);
v_i_391_ = v___x_399_;
v_b_393_ = v___x_397_;
goto _start;
}
else
{
return v_b_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0___boxed(lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_stop_403_, lean_object* v_b_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; lean_object* v_res_407_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_403_);
lean_dec(v_stop_403_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_as_401_, v_i_boxed_405_, v_stop_boxed_406_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t v_pu_408_, lean_object* v_lctx_409_, lean_object* v_ps_410_){
_start:
{
if (v_pu_408_ == 0)
{
lean_object* v_paramsPure_411_; lean_object* v_paramsImpure_412_; lean_object* v_letDeclsPure_413_; lean_object* v_letDeclsImpure_414_; lean_object* v_funDeclsPure_415_; lean_object* v_funDeclsImpure_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_paramsPure_411_ = lean_ctor_get(v_lctx_409_, 0);
v_paramsImpure_412_ = lean_ctor_get(v_lctx_409_, 1);
v_letDeclsPure_413_ = lean_ctor_get(v_lctx_409_, 2);
v_letDeclsImpure_414_ = lean_ctor_get(v_lctx_409_, 3);
v_funDeclsPure_415_ = lean_ctor_get(v_lctx_409_, 4);
v_funDeclsImpure_416_ = lean_ctor_get(v_lctx_409_, 5);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_array_get_size(v_ps_410_);
v___x_419_ = lean_nat_dec_lt(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
return v_lctx_409_;
}
else
{
uint8_t v___x_420_; 
v___x_420_ = lean_nat_dec_le(v___x_418_, v___x_418_);
if (v___x_420_ == 0)
{
if (v___x_419_ == 0)
{
return v_lctx_409_;
}
else
{
lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
lean_inc_ref(v_funDeclsImpure_416_);
lean_inc_ref(v_funDeclsPure_415_);
lean_inc_ref(v_letDeclsImpure_414_);
lean_inc_ref(v_letDeclsPure_413_);
lean_inc_ref(v_paramsImpure_412_);
lean_inc_ref(v_paramsPure_411_);
v_isSharedCheck_430_ = !lean_is_exclusive(v_lctx_409_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_431_ = lean_ctor_get(v_lctx_409_, 5);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_lctx_409_, 4);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_lctx_409_, 3);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_lctx_409_, 2);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_lctx_409_, 1);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_lctx_409_, 0);
lean_dec(v_unused_436_);
v___x_422_ = v_lctx_409_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_dec(v_lctx_409_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_424_ = ((size_t)0ULL);
v___x_425_ = lean_usize_of_nat(v___x_418_);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_410_, v___x_424_, v___x_425_, v_paramsPure_411_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_426_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_paramsImpure_412_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_letDeclsPure_413_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_letDeclsImpure_414_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_funDeclsPure_415_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v_funDeclsImpure_416_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
lean_inc_ref(v_funDeclsImpure_416_);
lean_inc_ref(v_funDeclsPure_415_);
lean_inc_ref(v_letDeclsImpure_414_);
lean_inc_ref(v_letDeclsPure_413_);
lean_inc_ref(v_paramsImpure_412_);
lean_inc_ref(v_paramsPure_411_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_lctx_409_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_447_ = lean_ctor_get(v_lctx_409_, 5);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_lctx_409_, 4);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_lctx_409_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_lctx_409_, 2);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_lctx_409_, 1);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_lctx_409_, 0);
lean_dec(v_unused_452_);
v___x_438_ = v_lctx_409_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_lctx_409_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_of_nat(v___x_418_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_410_, v___x_440_, v___x_441_, v_paramsPure_411_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_442_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_paramsImpure_412_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_letDeclsPure_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_letDeclsImpure_414_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_funDeclsPure_415_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v_funDeclsImpure_416_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
else
{
lean_object* v_paramsPure_453_; lean_object* v_paramsImpure_454_; lean_object* v_letDeclsPure_455_; lean_object* v_letDeclsImpure_456_; lean_object* v_funDeclsPure_457_; lean_object* v_funDeclsImpure_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_paramsPure_453_ = lean_ctor_get(v_lctx_409_, 0);
v_paramsImpure_454_ = lean_ctor_get(v_lctx_409_, 1);
v_letDeclsPure_455_ = lean_ctor_get(v_lctx_409_, 2);
v_letDeclsImpure_456_ = lean_ctor_get(v_lctx_409_, 3);
v_funDeclsPure_457_ = lean_ctor_get(v_lctx_409_, 4);
v_funDeclsImpure_458_ = lean_ctor_get(v_lctx_409_, 5);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_array_get_size(v_ps_410_);
v___x_461_ = lean_nat_dec_lt(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
return v_lctx_409_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = lean_nat_dec_le(v___x_460_, v___x_460_);
if (v___x_462_ == 0)
{
if (v___x_461_ == 0)
{
return v_lctx_409_;
}
else
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
lean_inc_ref(v_funDeclsImpure_458_);
lean_inc_ref(v_funDeclsPure_457_);
lean_inc_ref(v_letDeclsImpure_456_);
lean_inc_ref(v_letDeclsPure_455_);
lean_inc_ref(v_paramsImpure_454_);
lean_inc_ref(v_paramsPure_453_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_lctx_409_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_473_ = lean_ctor_get(v_lctx_409_, 5);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_lctx_409_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_lctx_409_, 3);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_lctx_409_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_lctx_409_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_lctx_409_, 0);
lean_dec(v_unused_478_);
v___x_464_ = v_lctx_409_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_dec(v_lctx_409_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_460_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_410_, v___x_466_, v___x_467_, v_paramsImpure_454_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_468_);
v___x_470_ = v___x_464_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_paramsPure_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_letDeclsPure_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_letDeclsImpure_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_funDeclsPure_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_funDeclsImpure_458_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_488_; 
lean_inc_ref(v_funDeclsImpure_458_);
lean_inc_ref(v_funDeclsPure_457_);
lean_inc_ref(v_letDeclsImpure_456_);
lean_inc_ref(v_letDeclsPure_455_);
lean_inc_ref(v_paramsImpure_454_);
lean_inc_ref(v_paramsPure_453_);
v_isSharedCheck_488_ = !lean_is_exclusive(v_lctx_409_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; lean_object* v_unused_490_; lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; lean_object* v_unused_494_; 
v_unused_489_ = lean_ctor_get(v_lctx_409_, 5);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_lctx_409_, 4);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_lctx_409_, 3);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_lctx_409_, 2);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_lctx_409_, 1);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_lctx_409_, 0);
lean_dec(v_unused_494_);
v___x_480_ = v_lctx_409_;
v_isShared_481_ = v_isSharedCheck_488_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_lctx_409_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_488_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_460_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_410_, v___x_482_, v___x_483_, v_paramsImpure_454_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_484_);
v___x_486_ = v___x_480_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_paramsPure_453_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_letDeclsPure_455_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_letDeclsImpure_456_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v_funDeclsPure_457_);
lean_ctor_set(v_reuseFailAlloc_487_, 5, v_funDeclsImpure_458_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(lean_object* v_pu_495_, lean_object* v_lctx_496_, lean_object* v_ps_497_){
_start:
{
uint8_t v_pu_boxed_498_; lean_object* v_res_499_; 
v_pu_boxed_498_ = lean_unbox(v_pu_495_);
v_res_499_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_boxed_498_, v_lctx_496_, v_ps_497_);
lean_dec_ref(v_ps_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t v_pu_500_, lean_object* v_lctx_501_, lean_object* v_decl_502_){
_start:
{
if (v_pu_500_ == 0)
{
lean_object* v_paramsPure_503_; lean_object* v_paramsImpure_504_; lean_object* v_letDeclsPure_505_; lean_object* v_letDeclsImpure_506_; lean_object* v_funDeclsPure_507_; lean_object* v_funDeclsImpure_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_517_; 
v_paramsPure_503_ = lean_ctor_get(v_lctx_501_, 0);
v_paramsImpure_504_ = lean_ctor_get(v_lctx_501_, 1);
v_letDeclsPure_505_ = lean_ctor_get(v_lctx_501_, 2);
v_letDeclsImpure_506_ = lean_ctor_get(v_lctx_501_, 3);
v_funDeclsPure_507_ = lean_ctor_get(v_lctx_501_, 4);
v_funDeclsImpure_508_ = lean_ctor_get(v_lctx_501_, 5);
v_isSharedCheck_517_ = !lean_is_exclusive(v_lctx_501_);
if (v_isSharedCheck_517_ == 0)
{
v___x_510_ = v_lctx_501_;
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_funDeclsImpure_508_);
lean_inc(v_funDeclsPure_507_);
lean_inc(v_letDeclsImpure_506_);
lean_inc(v_letDeclsPure_505_);
lean_inc(v_paramsImpure_504_);
lean_inc(v_paramsPure_503_);
lean_dec(v_lctx_501_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_fvarId_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v_fvarId_512_ = lean_ctor_get(v_decl_502_, 0);
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsPure_505_, v_fvarId_512_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 2, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_paramsPure_503_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_paramsImpure_504_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_letDeclsImpure_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_funDeclsPure_507_);
lean_ctor_set(v_reuseFailAlloc_516_, 5, v_funDeclsImpure_508_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v_paramsPure_518_; lean_object* v_paramsImpure_519_; lean_object* v_letDeclsPure_520_; lean_object* v_letDeclsImpure_521_; lean_object* v_funDeclsPure_522_; lean_object* v_funDeclsImpure_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
v_paramsPure_518_ = lean_ctor_get(v_lctx_501_, 0);
v_paramsImpure_519_ = lean_ctor_get(v_lctx_501_, 1);
v_letDeclsPure_520_ = lean_ctor_get(v_lctx_501_, 2);
v_letDeclsImpure_521_ = lean_ctor_get(v_lctx_501_, 3);
v_funDeclsPure_522_ = lean_ctor_get(v_lctx_501_, 4);
v_funDeclsImpure_523_ = lean_ctor_get(v_lctx_501_, 5);
v_isSharedCheck_532_ = !lean_is_exclusive(v_lctx_501_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v_lctx_501_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_funDeclsImpure_523_);
lean_inc(v_funDeclsPure_522_);
lean_inc(v_letDeclsImpure_521_);
lean_inc(v_letDeclsPure_520_);
lean_inc(v_paramsImpure_519_);
lean_inc(v_paramsPure_518_);
lean_dec(v_lctx_501_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_fvarId_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v_fvarId_527_ = lean_ctor_get(v_decl_502_, 0);
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsImpure_521_, v_fvarId_527_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 3, v___x_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_paramsPure_518_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_paramsImpure_519_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_letDeclsPure_520_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v_funDeclsPure_522_);
lean_ctor_set(v_reuseFailAlloc_531_, 5, v_funDeclsImpure_523_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(lean_object* v_pu_533_, lean_object* v_lctx_534_, lean_object* v_decl_535_){
_start:
{
uint8_t v_pu_boxed_536_; lean_object* v_res_537_; 
v_pu_boxed_536_ = lean_unbox(v_pu_533_);
v_res_537_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_boxed_536_, v_lctx_534_, v_decl_535_);
lean_dec_ref(v_decl_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t v_pu_538_, lean_object* v_lctx_539_, lean_object* v_decl_540_, uint8_t v_recursive_541_){
_start:
{
lean_object* v___y_543_; 
if (v_pu_538_ == 0)
{
lean_object* v_fvarId_548_; lean_object* v_paramsPure_549_; lean_object* v_paramsImpure_550_; lean_object* v_letDeclsPure_551_; lean_object* v_letDeclsImpure_552_; lean_object* v_funDeclsPure_553_; lean_object* v_funDeclsImpure_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_fvarId_548_ = lean_ctor_get(v_decl_540_, 0);
v_paramsPure_549_ = lean_ctor_get(v_lctx_539_, 0);
v_paramsImpure_550_ = lean_ctor_get(v_lctx_539_, 1);
v_letDeclsPure_551_ = lean_ctor_get(v_lctx_539_, 2);
v_letDeclsImpure_552_ = lean_ctor_get(v_lctx_539_, 3);
v_funDeclsPure_553_ = lean_ctor_get(v_lctx_539_, 4);
v_funDeclsImpure_554_ = lean_ctor_get(v_lctx_539_, 5);
v_isSharedCheck_562_ = !lean_is_exclusive(v_lctx_539_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v_lctx_539_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_funDeclsImpure_554_);
lean_inc(v_funDeclsPure_553_);
lean_inc(v_letDeclsImpure_552_);
lean_inc(v_letDeclsPure_551_);
lean_inc(v_paramsImpure_550_);
lean_inc(v_paramsPure_549_);
lean_dec(v_lctx_539_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsPure_553_, v_fvarId_548_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 4, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_paramsPure_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_paramsImpure_550_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_letDeclsPure_551_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_letDeclsImpure_552_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_funDeclsImpure_554_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v___y_543_ = v___x_560_;
goto v___jp_542_;
}
}
}
else
{
lean_object* v_fvarId_563_; lean_object* v_paramsPure_564_; lean_object* v_paramsImpure_565_; lean_object* v_letDeclsPure_566_; lean_object* v_letDeclsImpure_567_; lean_object* v_funDeclsPure_568_; lean_object* v_funDeclsImpure_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
v_fvarId_563_ = lean_ctor_get(v_decl_540_, 0);
v_paramsPure_564_ = lean_ctor_get(v_lctx_539_, 0);
v_paramsImpure_565_ = lean_ctor_get(v_lctx_539_, 1);
v_letDeclsPure_566_ = lean_ctor_get(v_lctx_539_, 2);
v_letDeclsImpure_567_ = lean_ctor_get(v_lctx_539_, 3);
v_funDeclsPure_568_ = lean_ctor_get(v_lctx_539_, 4);
v_funDeclsImpure_569_ = lean_ctor_get(v_lctx_539_, 5);
v_isSharedCheck_577_ = !lean_is_exclusive(v_lctx_539_);
if (v_isSharedCheck_577_ == 0)
{
v___x_571_ = v_lctx_539_;
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_funDeclsImpure_569_);
lean_inc(v_funDeclsPure_568_);
lean_inc(v_letDeclsImpure_567_);
lean_inc(v_letDeclsPure_566_);
lean_inc(v_paramsImpure_565_);
lean_inc(v_paramsPure_564_);
lean_dec(v_lctx_539_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsImpure_569_, v_fvarId_563_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 5, v___x_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_paramsPure_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_paramsImpure_565_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_letDeclsPure_566_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_letDeclsImpure_567_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_funDeclsPure_568_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v___y_543_ = v___x_575_;
goto v___jp_542_;
}
}
}
v___jp_542_:
{
if (v_recursive_541_ == 0)
{
return v___y_543_;
}
else
{
lean_object* v_params_544_; lean_object* v_value_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_params_544_ = lean_ctor_get(v_decl_540_, 2);
v_value_545_ = lean_ctor_get(v_decl_540_, 4);
v___x_546_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_538_, v___y_543_, v_params_544_);
v___x_547_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_538_, v_value_545_, v___x_546_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t v_pu_578_, lean_object* v_code_579_, lean_object* v_lctx_580_){
_start:
{
switch(lean_obj_tag(v_code_579_))
{
case 0:
{
lean_object* v_decl_581_; lean_object* v_k_582_; lean_object* v___x_583_; 
v_decl_581_ = lean_ctor_get(v_code_579_, 0);
v_k_582_ = lean_ctor_get(v_code_579_, 1);
v___x_583_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_578_, v_lctx_580_, v_decl_581_);
v_code_579_ = v_k_582_;
v_lctx_580_ = v___x_583_;
goto _start;
}
case 1:
{
lean_object* v_decl_585_; lean_object* v_k_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v_decl_585_ = lean_ctor_get(v_code_579_, 0);
v_k_586_ = lean_ctor_get(v_code_579_, 1);
v___x_587_ = 1;
v___x_588_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_578_, v_lctx_580_, v_decl_585_, v___x_587_);
v_code_579_ = v_k_586_;
v_lctx_580_ = v___x_588_;
goto _start;
}
case 2:
{
lean_object* v_decl_590_; lean_object* v_k_591_; uint8_t v___x_592_; lean_object* v___x_593_; 
v_decl_590_ = lean_ctor_get(v_code_579_, 0);
v_k_591_ = lean_ctor_get(v_code_579_, 1);
v___x_592_ = 1;
v___x_593_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_578_, v_lctx_580_, v_decl_590_, v___x_592_);
v_code_579_ = v_k_591_;
v_lctx_580_ = v___x_593_;
goto _start;
}
case 4:
{
lean_object* v_cases_595_; lean_object* v_alts_596_; lean_object* v___x_597_; 
v_cases_595_ = lean_ctor_get(v_code_579_, 0);
v_alts_596_ = lean_ctor_get(v_cases_595_, 3);
v___x_597_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_578_, v_alts_596_, v_lctx_580_);
return v___x_597_;
}
case 7:
{
lean_object* v_k_598_; 
v_k_598_ = lean_ctor_get(v_code_579_, 3);
v_code_579_ = v_k_598_;
goto _start;
}
case 8:
{
lean_object* v_k_600_; 
v_k_600_ = lean_ctor_get(v_code_579_, 3);
v_code_579_ = v_k_600_;
goto _start;
}
case 9:
{
lean_object* v_k_602_; 
v_k_602_ = lean_ctor_get(v_code_579_, 5);
v_code_579_ = v_k_602_;
goto _start;
}
case 10:
{
lean_object* v_k_604_; 
v_k_604_ = lean_ctor_get(v_code_579_, 2);
v_code_579_ = v_k_604_;
goto _start;
}
case 11:
{
lean_object* v_k_606_; 
v_k_606_ = lean_ctor_get(v_code_579_, 2);
v_code_579_ = v_k_606_;
goto _start;
}
case 12:
{
lean_object* v_k_608_; 
v_k_608_ = lean_ctor_get(v_code_579_, 3);
v_code_579_ = v_k_608_;
goto _start;
}
case 13:
{
lean_object* v_k_610_; 
v_k_610_ = lean_ctor_get(v_code_579_, 1);
v_code_579_ = v_k_610_;
goto _start;
}
default: 
{
return v_lctx_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(uint8_t v_pu_612_, lean_object* v_as_613_, size_t v_i_614_, size_t v_stop_615_, lean_object* v_b_616_){
_start:
{
lean_object* v___y_618_; uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_614_, v_stop_615_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_array_uget_borrowed(v_as_613_, v_i_614_);
switch(lean_obj_tag(v___x_623_))
{
case 0:
{
lean_object* v_params_624_; lean_object* v_code_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_params_624_ = lean_ctor_get(v___x_623_, 1);
v_code_625_ = lean_ctor_get(v___x_623_, 2);
v___x_626_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_612_, v_b_616_, v_params_624_);
v___x_627_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_612_, v_code_625_, v___x_626_);
v___y_618_ = v___x_627_;
goto v___jp_617_;
}
case 1:
{
lean_object* v_code_628_; lean_object* v___x_629_; 
v_code_628_ = lean_ctor_get(v___x_623_, 1);
v___x_629_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_612_, v_code_628_, v_b_616_);
v___y_618_ = v___x_629_;
goto v___jp_617_;
}
default: 
{
lean_object* v_code_630_; lean_object* v___x_631_; 
v_code_630_ = lean_ctor_get(v___x_623_, 0);
v___x_631_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_612_, v_code_630_, v_b_616_);
v___y_618_ = v___x_631_;
goto v___jp_617_;
}
}
}
else
{
return v_b_616_;
}
v___jp_617_:
{
size_t v___x_619_; size_t v___x_620_; 
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_614_, v___x_619_);
v_i_614_ = v___x_620_;
v_b_616_ = v___y_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts(uint8_t v_pu_632_, lean_object* v_alts_633_, lean_object* v_lctx_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_array_get_size(v_alts_633_);
v___x_637_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
return v_lctx_634_;
}
else
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_le(v___x_636_, v___x_636_);
if (v___x_638_ == 0)
{
if (v___x_637_ == 0)
{
return v_lctx_634_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lean_usize_of_nat(v___x_636_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_632_, v_alts_633_, v___x_639_, v___x_640_, v_lctx_634_);
return v___x_641_;
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_636_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_632_, v_alts_633_, v___x_642_, v___x_643_, v_lctx_634_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(lean_object* v_pu_645_, lean_object* v_alts_646_, lean_object* v_lctx_647_){
_start:
{
uint8_t v_pu_boxed_648_; lean_object* v_res_649_; 
v_pu_boxed_648_ = lean_unbox(v_pu_645_);
v_res_649_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_boxed_648_, v_alts_646_, v_lctx_647_);
lean_dec_ref(v_alts_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(lean_object* v_pu_650_, lean_object* v_as_651_, lean_object* v_i_652_, lean_object* v_stop_653_, lean_object* v_b_654_){
_start:
{
uint8_t v_pu_boxed_655_; size_t v_i_boxed_656_; size_t v_stop_boxed_657_; lean_object* v_res_658_; 
v_pu_boxed_655_ = lean_unbox(v_pu_650_);
v_i_boxed_656_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v_stop_boxed_657_ = lean_unbox_usize(v_stop_653_);
lean_dec(v_stop_653_);
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_boxed_655_, v_as_651_, v_i_boxed_656_, v_stop_boxed_657_, v_b_654_);
lean_dec_ref(v_as_651_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(lean_object* v_pu_659_, lean_object* v_lctx_660_, lean_object* v_decl_661_, lean_object* v_recursive_662_){
_start:
{
uint8_t v_pu_boxed_663_; uint8_t v_recursive_boxed_664_; lean_object* v_res_665_; 
v_pu_boxed_663_ = lean_unbox(v_pu_659_);
v_recursive_boxed_664_ = lean_unbox(v_recursive_662_);
v_res_665_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_boxed_663_, v_lctx_660_, v_decl_661_, v_recursive_boxed_664_);
lean_dec_ref(v_decl_661_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(lean_object* v_pu_666_, lean_object* v_code_667_, lean_object* v_lctx_668_){
_start:
{
uint8_t v_pu_boxed_669_; lean_object* v_res_670_; 
v_pu_boxed_669_ = lean_unbox(v_pu_666_);
v_res_670_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_boxed_669_, v_code_667_, v_lctx_668_);
lean_dec_ref(v_code_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params(lean_object* v_lctx_671_, uint8_t v_pu_672_){
_start:
{
if (v_pu_672_ == 0)
{
lean_object* v_paramsPure_673_; 
v_paramsPure_673_ = lean_ctor_get(v_lctx_671_, 0);
lean_inc_ref(v_paramsPure_673_);
return v_paramsPure_673_;
}
else
{
lean_object* v_paramsImpure_674_; 
v_paramsImpure_674_ = lean_ctor_get(v_lctx_671_, 1);
lean_inc_ref(v_paramsImpure_674_);
return v_paramsImpure_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params___boxed(lean_object* v_lctx_675_, lean_object* v_pu_676_){
_start:
{
uint8_t v_pu_boxed_677_; lean_object* v_res_678_; 
v_pu_boxed_677_ = lean_unbox(v_pu_676_);
v_res_678_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_675_, v_pu_boxed_677_);
lean_dec_ref(v_lctx_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls(lean_object* v_lctx_679_, uint8_t v_pu_680_){
_start:
{
if (v_pu_680_ == 0)
{
lean_object* v_letDeclsPure_681_; 
v_letDeclsPure_681_ = lean_ctor_get(v_lctx_679_, 2);
lean_inc_ref(v_letDeclsPure_681_);
return v_letDeclsPure_681_;
}
else
{
lean_object* v_letDeclsImpure_682_; 
v_letDeclsImpure_682_ = lean_ctor_get(v_lctx_679_, 3);
lean_inc_ref(v_letDeclsImpure_682_);
return v_letDeclsImpure_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(lean_object* v_lctx_683_, lean_object* v_pu_684_){
_start:
{
uint8_t v_pu_boxed_685_; lean_object* v_res_686_; 
v_pu_boxed_685_ = lean_unbox(v_pu_684_);
v_res_686_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_683_, v_pu_boxed_685_);
lean_dec_ref(v_lctx_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls(lean_object* v_lctx_687_, uint8_t v_pu_688_){
_start:
{
if (v_pu_688_ == 0)
{
lean_object* v_funDeclsPure_689_; 
v_funDeclsPure_689_ = lean_ctor_get(v_lctx_687_, 4);
lean_inc_ref(v_funDeclsPure_689_);
return v_funDeclsPure_689_;
}
else
{
lean_object* v_funDeclsImpure_690_; 
v_funDeclsImpure_690_ = lean_ctor_get(v_lctx_687_, 5);
lean_inc_ref(v_funDeclsImpure_690_);
return v_funDeclsImpure_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(lean_object* v_lctx_691_, lean_object* v_pu_692_){
_start:
{
uint8_t v_pu_boxed_693_; lean_object* v_res_694_; 
v_pu_boxed_693_ = lean_unbox(v_pu_692_);
v_res_694_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_691_, v_pu_boxed_693_);
lean_dec_ref(v_lctx_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
if (lean_obj_tag(v_a_695_) == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_a_696_);
return v___x_697_;
}
else
{
lean_object* v_value_698_; lean_object* v_tail_699_; lean_object* v_fvarId_700_; lean_object* v_binderName_701_; lean_object* v_type_702_; lean_object* v___x_703_; uint8_t v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_value_698_ = lean_ctor_get(v_a_695_, 1);
v_tail_699_ = lean_ctor_get(v_a_695_, 2);
v_fvarId_700_ = lean_ctor_get(v_value_698_, 0);
v_binderName_701_ = lean_ctor_get(v_value_698_, 1);
v_type_702_ = lean_ctor_get(v_value_698_, 3);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = 0;
v___x_705_ = 0;
lean_inc_ref(v_type_702_);
lean_inc(v_binderName_701_);
lean_inc(v_fvarId_700_);
v___x_706_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_706_, 0, v___x_703_);
lean_ctor_set(v___x_706_, 1, v_fvarId_700_);
lean_ctor_set(v___x_706_, 2, v_binderName_701_);
lean_ctor_set(v___x_706_, 3, v_type_702_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*4, v___x_704_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*4 + 1, v___x_705_);
v___x_707_ = l_Lean_LocalContext_addDecl(v_a_696_, v___x_706_);
v_a_695_ = v_tail_699_;
v_a_696_ = v___x_707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_709_, v_a_710_);
lean_dec(v_a_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(lean_object* v_as_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_b_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_716_ == 0)
{
return v_b_715_;
}
else
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_array_uget_borrowed(v_as_712_, v_i_714_);
v___x_718_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_717_, v_b_715_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
return v_a_719_;
}
else
{
lean_object* v_a_720_; size_t v___x_721_; size_t v___x_722_; 
v_a_720_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_718_, 1);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_714_, v___x_721_);
v_i_714_ = v___x_722_;
v_b_715_ = v_a_720_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5___boxed(lean_object* v_as_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_b_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_as_724_, v_sz_boxed_728_, v_i_boxed_729_, v_b_727_);
lean_dec_ref(v_as_724_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(uint8_t v_pu_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
if (lean_obj_tag(v_a_732_) == 0)
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_a_733_);
return v___x_734_;
}
else
{
lean_object* v_value_735_; lean_object* v_tail_736_; lean_object* v_fvarId_737_; lean_object* v_binderName_738_; lean_object* v_type_739_; lean_object* v_value_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_value_735_ = lean_ctor_get(v_a_732_, 1);
lean_inc(v_value_735_);
v_tail_736_ = lean_ctor_get(v_a_732_, 2);
lean_inc(v_tail_736_);
lean_dec_ref_known(v_a_732_, 3);
v_fvarId_737_ = lean_ctor_get(v_value_735_, 0);
lean_inc(v_fvarId_737_);
v_binderName_738_ = lean_ctor_get(v_value_735_, 1);
lean_inc(v_binderName_738_);
v_type_739_ = lean_ctor_get(v_value_735_, 2);
lean_inc_ref(v_type_739_);
v_value_740_ = lean_ctor_get(v_value_735_, 3);
lean_inc(v_value_740_);
lean_dec(v_value_735_);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_731_, v_value_740_);
v___x_743_ = 1;
v___x_744_ = 0;
v___x_745_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_745_, 0, v___x_741_);
lean_ctor_set(v___x_745_, 1, v_fvarId_737_);
lean_ctor_set(v___x_745_, 2, v_binderName_738_);
lean_ctor_set(v___x_745_, 3, v_type_739_);
lean_ctor_set(v___x_745_, 4, v___x_742_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*5, v___x_743_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*5 + 1, v___x_744_);
v___x_746_ = l_Lean_LocalContext_addDecl(v_a_733_, v___x_745_);
v_a_732_ = v_tail_736_;
v_a_733_ = v___x_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object* v_pu_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
uint8_t v_pu_boxed_751_; lean_object* v_res_752_; 
v_pu_boxed_751_ = lean_unbox(v_pu_748_);
v_res_752_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_boxed_751_, v_a_749_, v_a_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(uint8_t v_pu_753_, lean_object* v_as_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_b_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = lean_usize_dec_lt(v_i_756_, v_sz_755_);
if (v___x_758_ == 0)
{
return v_b_757_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_array_uget_borrowed(v_as_754_, v_i_756_);
lean_inc(v_a_759_);
v___x_760_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_753_, v_a_759_, v_b_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
return v_a_761_;
}
else
{
lean_object* v_a_762_; size_t v___x_763_; size_t v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_760_, 1);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_756_, v___x_763_);
v_i_756_ = v___x_764_;
v_b_757_ = v_a_762_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4___boxed(lean_object* v_pu_766_, lean_object* v_as_767_, lean_object* v_sz_768_, lean_object* v_i_769_, lean_object* v_b_770_){
_start:
{
uint8_t v_pu_boxed_771_; size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_pu_boxed_771_ = lean_unbox(v_pu_766_);
v_sz_boxed_772_ = lean_unbox_usize(v_sz_768_);
lean_dec(v_sz_768_);
v_i_boxed_773_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_boxed_771_, v_as_767_, v_sz_boxed_772_, v_i_boxed_773_, v_b_770_);
lean_dec_ref(v_as_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
if (lean_obj_tag(v_a_775_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_a_776_);
return v___x_777_;
}
else
{
lean_object* v_value_778_; lean_object* v_tail_779_; lean_object* v_fvarId_780_; lean_object* v_binderName_781_; lean_object* v_type_782_; lean_object* v___x_783_; uint8_t v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_value_778_ = lean_ctor_get(v_a_775_, 1);
v_tail_779_ = lean_ctor_get(v_a_775_, 2);
v_fvarId_780_ = lean_ctor_get(v_value_778_, 0);
v_binderName_781_ = lean_ctor_get(v_value_778_, 1);
v_type_782_ = lean_ctor_get(v_value_778_, 2);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = 0;
v___x_785_ = 0;
lean_inc_ref(v_type_782_);
lean_inc(v_binderName_781_);
lean_inc(v_fvarId_780_);
v___x_786_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v_fvarId_780_);
lean_ctor_set(v___x_786_, 2, v_binderName_781_);
lean_ctor_set(v___x_786_, 3, v_type_782_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*4, v___x_784_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*4 + 1, v___x_785_);
v___x_787_ = l_Lean_LocalContext_addDecl(v_a_776_, v___x_786_);
v_a_775_ = v_tail_779_;
v_a_776_ = v___x_787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_789_, v_a_790_);
lean_dec(v_a_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(lean_object* v_as_792_, size_t v_sz_793_, size_t v_i_794_, lean_object* v_b_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_796_ == 0)
{
return v_b_795_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_array_uget_borrowed(v_as_792_, v_i_794_);
v___x_798_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_797_, v_b_795_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
return v_a_799_;
}
else
{
lean_object* v_a_800_; size_t v___x_801_; size_t v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_798_, 1);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_794_, v___x_801_);
v_i_794_ = v___x_802_;
v_b_795_ = v_a_800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3___boxed(lean_object* v_as_804_, lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_b_807_){
_start:
{
size_t v_sz_boxed_808_; size_t v_i_boxed_809_; lean_object* v_res_810_; 
v_sz_boxed_808_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_as_804_, v_sz_boxed_808_, v_i_boxed_809_, v_b_807_);
lean_dec_ref(v_as_804_);
return v_res_810_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_unsigned_to_nat(32u);
v___x_815_ = lean_mk_empty_array_with_capacity(v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3(void){
_start:
{
size_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_817_ = ((size_t)5ULL);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_unsigned_to_nat(32u);
v___x_820_ = lean_mk_empty_array_with_capacity(v___x_819_);
v___x_821_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2);
v___x_822_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_820_);
lean_ctor_set(v___x_822_, 2, v___x_818_);
lean_ctor_set(v___x_822_, 3, v___x_818_);
lean_ctor_set_usize(v___x_822_, 4, v___x_817_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_result_826_; 
v___x_823_ = lean_box(1);
v___x_824_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3);
v___x_825_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1);
v_result_826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_826_, 0, v___x_825_);
lean_ctor_set(v_result_826_, 1, v___x_824_);
lean_ctor_set(v_result_826_, 2, v___x_823_);
return v_result_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object* v_lctx_827_, uint8_t v_pu_828_){
_start:
{
size_t v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; size_t v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v_result_845_; lean_object* v___y_847_; 
v_result_845_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4);
if (v_pu_828_ == 0)
{
lean_object* v_paramsPure_854_; 
v_paramsPure_854_ = lean_ctor_get(v_lctx_827_, 0);
v___y_847_ = v_paramsPure_854_;
goto v___jp_846_;
}
else
{
lean_object* v_paramsImpure_855_; 
v_paramsImpure_855_ = lean_ctor_get(v_lctx_827_, 1);
v___y_847_ = v_paramsImpure_855_;
goto v___jp_846_;
}
v___jp_829_:
{
lean_object* v_buckets_833_; size_t v_sz_834_; lean_object* v___x_835_; 
v_buckets_833_ = lean_ctor_get(v___y_832_, 1);
v_sz_834_ = lean_array_size(v_buckets_833_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_buckets_833_, v_sz_834_, v___y_830_, v___y_831_);
return v___x_835_;
}
v___jp_836_:
{
lean_object* v_buckets_840_; size_t v_sz_841_; lean_object* v___x_842_; 
v_buckets_840_ = lean_ctor_get(v___y_839_, 1);
v_sz_841_ = lean_array_size(v_buckets_840_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_828_, v_buckets_840_, v_sz_841_, v___y_837_, v___y_838_);
if (v_pu_828_ == 0)
{
lean_object* v_funDeclsPure_843_; 
v_funDeclsPure_843_ = lean_ctor_get(v_lctx_827_, 4);
v___y_830_ = v___y_837_;
v___y_831_ = v___x_842_;
v___y_832_ = v_funDeclsPure_843_;
goto v___jp_829_;
}
else
{
lean_object* v_funDeclsImpure_844_; 
v_funDeclsImpure_844_ = lean_ctor_get(v_lctx_827_, 5);
v___y_830_ = v___y_837_;
v___y_831_ = v___x_842_;
v___y_832_ = v_funDeclsImpure_844_;
goto v___jp_829_;
}
}
v___jp_846_:
{
lean_object* v_buckets_848_; size_t v_sz_849_; size_t v___x_850_; lean_object* v___x_851_; 
v_buckets_848_ = lean_ctor_get(v___y_847_, 1);
v_sz_849_ = lean_array_size(v_buckets_848_);
v___x_850_ = ((size_t)0ULL);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_buckets_848_, v_sz_849_, v___x_850_, v_result_845_);
if (v_pu_828_ == 0)
{
lean_object* v_letDeclsPure_852_; 
v_letDeclsPure_852_ = lean_ctor_get(v_lctx_827_, 2);
v___y_837_ = v___x_850_;
v___y_838_ = v___x_851_;
v___y_839_ = v_letDeclsPure_852_;
goto v___jp_836_;
}
else
{
lean_object* v_letDeclsImpure_853_; 
v_letDeclsImpure_853_ = lean_ctor_get(v_lctx_827_, 3);
v___y_837_ = v___x_850_;
v___y_838_ = v___x_851_;
v___y_839_ = v_letDeclsImpure_853_;
goto v___jp_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(lean_object* v_lctx_856_, lean_object* v_pu_857_){
_start:
{
uint8_t v_pu_boxed_858_; lean_object* v_res_859_; 
v_pu_boxed_858_ = lean_unbox(v_pu_857_);
v_res_859_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_856_, v_pu_boxed_858_);
lean_dec_ref(v_lctx_856_);
return v_res_859_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedLCtx_default = _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLCtx_default);
l_Lean_Compiler_LCNF_instInhabitedLCtx = _init_l_Lean_Compiler_LCNF_instInhabitedLCtx();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLCtx);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_LCtx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_LCtx(builtin);
}
#ifdef __cplusplus
}
#endif
