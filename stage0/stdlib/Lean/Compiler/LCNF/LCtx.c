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
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_nbuckets_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_63_ = lean_array_get_size(v_data_62_);
v___x_64_ = lean_unsigned_to_nat(2u);
v_nbuckets_65_ = lean_nat_mul(v___x_63_, v___x_64_);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_box(0);
v___x_68_ = lean_mk_array(v_nbuckets_65_, v___x_67_);
v___x_69_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v___x_66_, v_data_62_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(lean_object* v_a_70_, lean_object* v_b_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_dec(v_b_71_);
lean_dec(v_a_70_);
return v_x_72_;
}
else
{
lean_object* v_key_73_; lean_object* v_value_74_; lean_object* v_tail_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_87_; 
v_key_73_ = lean_ctor_get(v_x_72_, 0);
v_value_74_ = lean_ctor_get(v_x_72_, 1);
v_tail_75_ = lean_ctor_get(v_x_72_, 2);
v_isSharedCheck_87_ = !lean_is_exclusive(v_x_72_);
if (v_isSharedCheck_87_ == 0)
{
v___x_77_ = v_x_72_;
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_tail_75_);
lean_inc(v_value_74_);
lean_inc(v_key_73_);
lean_dec(v_x_72_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; 
v___x_79_ = l_Lean_instBEqFVarId_beq(v_key_73_, v_a_70_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_70_, v_b_71_, v_tail_75_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 2, v___x_80_);
v___x_82_ = v___x_77_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_key_73_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_value_74_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
else
{
lean_object* v___x_85_; 
lean_dec(v_value_74_);
lean_dec(v_key_73_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v_b_71_);
lean_ctor_set(v___x_77_, 0, v_a_70_);
v___x_85_ = v___x_77_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_b_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_tail_75_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object* v_m_88_, lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
lean_object* v_size_91_; lean_object* v_buckets_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_135_; 
v_size_91_ = lean_ctor_get(v_m_88_, 0);
v_buckets_92_ = lean_ctor_get(v_m_88_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_m_88_);
if (v_isSharedCheck_135_ == 0)
{
v___x_94_ = v_m_88_;
v_isShared_95_ = v_isSharedCheck_135_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_buckets_92_);
lean_inc(v_size_91_);
lean_dec(v_m_88_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_135_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; uint64_t v_fold_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; lean_object* v_bkt_109_; uint8_t v___x_110_; 
v___x_96_ = lean_array_get_size(v_buckets_92_);
v___x_97_ = l_Lean_instHashableFVarId_hash(v_a_89_);
v___x_98_ = 32ULL;
v___x_99_ = lean_uint64_shift_right(v___x_97_, v___x_98_);
v_fold_100_ = lean_uint64_xor(v___x_97_, v___x_99_);
v___x_101_ = 16ULL;
v___x_102_ = lean_uint64_shift_right(v_fold_100_, v___x_101_);
v___x_103_ = lean_uint64_xor(v_fold_100_, v___x_102_);
v___x_104_ = lean_uint64_to_usize(v___x_103_);
v___x_105_ = lean_usize_of_nat(v___x_96_);
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_sub(v___x_105_, v___x_106_);
v___x_108_ = lean_usize_land(v___x_104_, v___x_107_);
v_bkt_109_ = lean_array_uget_borrowed(v_buckets_92_, v___x_108_);
v___x_110_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_89_, v_bkt_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v_size_x27_112_; lean_object* v___x_113_; lean_object* v_buckets_x27_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v_size_x27_112_ = lean_nat_add(v_size_91_, v___x_111_);
lean_dec(v_size_91_);
lean_inc(v_bkt_109_);
v___x_113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_113_, 0, v_a_89_);
lean_ctor_set(v___x_113_, 1, v_b_90_);
lean_ctor_set(v___x_113_, 2, v_bkt_109_);
v_buckets_x27_114_ = lean_array_uset(v_buckets_92_, v___x_108_, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(4u);
v___x_116_ = lean_nat_mul(v_size_x27_112_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_118_ = lean_nat_div(v___x_116_, v___x_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_array_get_size(v_buckets_x27_114_);
v___x_120_ = lean_nat_dec_le(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
if (v___x_120_ == 0)
{
lean_object* v_val_121_; lean_object* v___x_123_; 
v_val_121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_buckets_x27_114_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_val_121_);
lean_ctor_set(v___x_94_, 0, v_size_x27_112_);
v___x_123_ = v___x_94_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_size_x27_112_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_val_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
else
{
lean_object* v___x_126_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_buckets_x27_114_);
lean_ctor_set(v___x_94_, 0, v_size_x27_112_);
v___x_126_ = v___x_94_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_size_x27_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_buckets_x27_114_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v___x_128_; lean_object* v_buckets_x27_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_inc(v_bkt_109_);
v___x_128_ = lean_box(0);
v_buckets_x27_129_ = lean_array_uset(v_buckets_92_, v___x_108_, v___x_128_);
v___x_130_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_89_, v_b_90_, v_bkt_109_);
v___x_131_ = lean_array_uset(v_buckets_x27_129_, v___x_108_, v___x_130_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v___x_131_);
v___x_133_ = v___x_94_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_size_91_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_131_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t v_pu_136_, lean_object* v_lctx_137_, lean_object* v_param_138_){
_start:
{
if (v_pu_136_ == 0)
{
lean_object* v_paramsPure_139_; lean_object* v_paramsImpure_140_; lean_object* v_letDeclsPure_141_; lean_object* v_letDeclsImpure_142_; lean_object* v_funDeclsPure_143_; lean_object* v_funDeclsImpure_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v_paramsPure_139_ = lean_ctor_get(v_lctx_137_, 0);
v_paramsImpure_140_ = lean_ctor_get(v_lctx_137_, 1);
v_letDeclsPure_141_ = lean_ctor_get(v_lctx_137_, 2);
v_letDeclsImpure_142_ = lean_ctor_get(v_lctx_137_, 3);
v_funDeclsPure_143_ = lean_ctor_get(v_lctx_137_, 4);
v_funDeclsImpure_144_ = lean_ctor_get(v_lctx_137_, 5);
v_isSharedCheck_153_ = !lean_is_exclusive(v_lctx_137_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v_lctx_137_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_funDeclsImpure_144_);
lean_inc(v_funDeclsPure_143_);
lean_inc(v_letDeclsImpure_142_);
lean_inc(v_letDeclsPure_141_);
lean_inc(v_paramsImpure_140_);
lean_inc(v_paramsPure_139_);
lean_dec(v_lctx_137_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_fvarId_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v_fvarId_148_ = lean_ctor_get(v_param_138_, 0);
lean_inc(v_fvarId_148_);
v___x_149_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsPure_139_, v_fvarId_148_, v_param_138_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_paramsImpure_140_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_letDeclsPure_141_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_letDeclsImpure_142_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_funDeclsPure_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 5, v_funDeclsImpure_144_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_paramsPure_154_; lean_object* v_paramsImpure_155_; lean_object* v_letDeclsPure_156_; lean_object* v_letDeclsImpure_157_; lean_object* v_funDeclsPure_158_; lean_object* v_funDeclsImpure_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_168_; 
v_paramsPure_154_ = lean_ctor_get(v_lctx_137_, 0);
v_paramsImpure_155_ = lean_ctor_get(v_lctx_137_, 1);
v_letDeclsPure_156_ = lean_ctor_get(v_lctx_137_, 2);
v_letDeclsImpure_157_ = lean_ctor_get(v_lctx_137_, 3);
v_funDeclsPure_158_ = lean_ctor_get(v_lctx_137_, 4);
v_funDeclsImpure_159_ = lean_ctor_get(v_lctx_137_, 5);
v_isSharedCheck_168_ = !lean_is_exclusive(v_lctx_137_);
if (v_isSharedCheck_168_ == 0)
{
v___x_161_ = v_lctx_137_;
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_funDeclsImpure_159_);
lean_inc(v_funDeclsPure_158_);
lean_inc(v_letDeclsImpure_157_);
lean_inc(v_letDeclsPure_156_);
lean_inc(v_paramsImpure_155_);
lean_inc(v_paramsPure_154_);
lean_dec(v_lctx_137_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_fvarId_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v_fvarId_163_ = lean_ctor_get(v_param_138_, 0);
lean_inc(v_fvarId_163_);
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsImpure_155_, v_fvarId_163_, v_param_138_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_164_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_paramsPure_154_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_letDeclsPure_156_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_funDeclsPure_158_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_funDeclsImpure_159_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam___boxed(lean_object* v_pu_169_, lean_object* v_lctx_170_, lean_object* v_param_171_){
_start:
{
uint8_t v_pu_boxed_172_; lean_object* v_res_173_; 
v_pu_boxed_172_ = lean_unbox(v_pu_169_);
v_res_173_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_boxed_172_, v_lctx_170_, v_param_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object* v_00_u03b2_174_, lean_object* v_m_175_, lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_175_, v_a_176_, v_b_177_);
return v___x_178_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_object* v_00_u03b2_179_, lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_180_, v_x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_183_, lean_object* v_a_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(v_00_u03b2_183_, v_a_184_, v_x_185_);
lean_dec(v_x_185_);
lean_dec(v_a_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1(lean_object* v_00_u03b2_188_, lean_object* v_data_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_data_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2(lean_object* v_00_u03b2_191_, lean_object* v_a_192_, lean_object* v_b_193_, lean_object* v_x_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_192_, v_b_193_, v_x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_196_, lean_object* v_i_197_, lean_object* v_source_198_, lean_object* v_target_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v_i_197_, v_source_198_, v_target_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_x_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t v_pu_205_, lean_object* v_lctx_206_, lean_object* v_letDecl_207_){
_start:
{
if (v_pu_205_ == 0)
{
lean_object* v_paramsPure_208_; lean_object* v_paramsImpure_209_; lean_object* v_letDeclsPure_210_; lean_object* v_letDeclsImpure_211_; lean_object* v_funDeclsPure_212_; lean_object* v_funDeclsImpure_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_222_; 
v_paramsPure_208_ = lean_ctor_get(v_lctx_206_, 0);
v_paramsImpure_209_ = lean_ctor_get(v_lctx_206_, 1);
v_letDeclsPure_210_ = lean_ctor_get(v_lctx_206_, 2);
v_letDeclsImpure_211_ = lean_ctor_get(v_lctx_206_, 3);
v_funDeclsPure_212_ = lean_ctor_get(v_lctx_206_, 4);
v_funDeclsImpure_213_ = lean_ctor_get(v_lctx_206_, 5);
v_isSharedCheck_222_ = !lean_is_exclusive(v_lctx_206_);
if (v_isSharedCheck_222_ == 0)
{
v___x_215_ = v_lctx_206_;
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_funDeclsImpure_213_);
lean_inc(v_funDeclsPure_212_);
lean_inc(v_letDeclsImpure_211_);
lean_inc(v_letDeclsPure_210_);
lean_inc(v_paramsImpure_209_);
lean_inc(v_paramsPure_208_);
lean_dec(v_lctx_206_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fvarId_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v_fvarId_217_ = lean_ctor_get(v_letDecl_207_, 0);
lean_inc(v_fvarId_217_);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsPure_210_, v_fvarId_217_, v_letDecl_207_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 2, v___x_218_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_paramsPure_208_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_paramsImpure_209_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v_letDeclsImpure_211_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_funDeclsPure_212_);
lean_ctor_set(v_reuseFailAlloc_221_, 5, v_funDeclsImpure_213_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v_paramsPure_223_; lean_object* v_paramsImpure_224_; lean_object* v_letDeclsPure_225_; lean_object* v_letDeclsImpure_226_; lean_object* v_funDeclsPure_227_; lean_object* v_funDeclsImpure_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
v_paramsPure_223_ = lean_ctor_get(v_lctx_206_, 0);
v_paramsImpure_224_ = lean_ctor_get(v_lctx_206_, 1);
v_letDeclsPure_225_ = lean_ctor_get(v_lctx_206_, 2);
v_letDeclsImpure_226_ = lean_ctor_get(v_lctx_206_, 3);
v_funDeclsPure_227_ = lean_ctor_get(v_lctx_206_, 4);
v_funDeclsImpure_228_ = lean_ctor_get(v_lctx_206_, 5);
v_isSharedCheck_237_ = !lean_is_exclusive(v_lctx_206_);
if (v_isSharedCheck_237_ == 0)
{
v___x_230_ = v_lctx_206_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_funDeclsImpure_228_);
lean_inc(v_funDeclsPure_227_);
lean_inc(v_letDeclsImpure_226_);
lean_inc(v_letDeclsPure_225_);
lean_inc(v_paramsImpure_224_);
lean_inc(v_paramsPure_223_);
lean_dec(v_lctx_206_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_fvarId_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v_fvarId_232_ = lean_ctor_get(v_letDecl_207_, 0);
lean_inc(v_fvarId_232_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsImpure_226_, v_fvarId_232_, v_letDecl_207_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 3, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_paramsPure_223_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_paramsImpure_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_letDeclsPure_225_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_funDeclsPure_227_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v_funDeclsImpure_228_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(lean_object* v_pu_238_, lean_object* v_lctx_239_, lean_object* v_letDecl_240_){
_start:
{
uint8_t v_pu_boxed_241_; lean_object* v_res_242_; 
v_pu_boxed_241_ = lean_unbox(v_pu_238_);
v_res_242_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_boxed_241_, v_lctx_239_, v_letDecl_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t v_pu_243_, lean_object* v_lctx_244_, lean_object* v_funDecl_245_){
_start:
{
if (v_pu_243_ == 0)
{
lean_object* v_fvarId_246_; lean_object* v_paramsPure_247_; lean_object* v_paramsImpure_248_; lean_object* v_letDeclsPure_249_; lean_object* v_letDeclsImpure_250_; lean_object* v_funDeclsPure_251_; lean_object* v_funDeclsImpure_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_fvarId_246_ = lean_ctor_get(v_funDecl_245_, 0);
lean_inc(v_fvarId_246_);
v_paramsPure_247_ = lean_ctor_get(v_lctx_244_, 0);
v_paramsImpure_248_ = lean_ctor_get(v_lctx_244_, 1);
v_letDeclsPure_249_ = lean_ctor_get(v_lctx_244_, 2);
v_letDeclsImpure_250_ = lean_ctor_get(v_lctx_244_, 3);
v_funDeclsPure_251_ = lean_ctor_get(v_lctx_244_, 4);
v_funDeclsImpure_252_ = lean_ctor_get(v_lctx_244_, 5);
v_isSharedCheck_260_ = !lean_is_exclusive(v_lctx_244_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v_lctx_244_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_funDeclsImpure_252_);
lean_inc(v_funDeclsPure_251_);
lean_inc(v_letDeclsImpure_250_);
lean_inc(v_letDeclsPure_249_);
lean_inc(v_paramsImpure_248_);
lean_inc(v_paramsPure_247_);
lean_dec(v_lctx_244_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsPure_251_, v_fvarId_246_, v_funDecl_245_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_paramsPure_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_paramsImpure_248_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_letDeclsPure_249_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_letDeclsImpure_250_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_259_, 5, v_funDeclsImpure_252_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_fvarId_261_; lean_object* v_paramsPure_262_; lean_object* v_paramsImpure_263_; lean_object* v_letDeclsPure_264_; lean_object* v_letDeclsImpure_265_; lean_object* v_funDeclsPure_266_; lean_object* v_funDeclsImpure_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_275_; 
v_fvarId_261_ = lean_ctor_get(v_funDecl_245_, 0);
lean_inc(v_fvarId_261_);
v_paramsPure_262_ = lean_ctor_get(v_lctx_244_, 0);
v_paramsImpure_263_ = lean_ctor_get(v_lctx_244_, 1);
v_letDeclsPure_264_ = lean_ctor_get(v_lctx_244_, 2);
v_letDeclsImpure_265_ = lean_ctor_get(v_lctx_244_, 3);
v_funDeclsPure_266_ = lean_ctor_get(v_lctx_244_, 4);
v_funDeclsImpure_267_ = lean_ctor_get(v_lctx_244_, 5);
v_isSharedCheck_275_ = !lean_is_exclusive(v_lctx_244_);
if (v_isSharedCheck_275_ == 0)
{
v___x_269_ = v_lctx_244_;
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_funDeclsImpure_267_);
lean_inc(v_funDeclsPure_266_);
lean_inc(v_letDeclsImpure_265_);
lean_inc(v_letDeclsPure_264_);
lean_inc(v_paramsImpure_263_);
lean_inc(v_paramsPure_262_);
lean_dec(v_lctx_244_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsImpure_267_, v_fvarId_261_, v_funDecl_245_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 5, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_paramsPure_262_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_paramsImpure_263_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_letDeclsPure_264_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_letDeclsImpure_265_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_funDeclsPure_266_);
lean_ctor_set(v_reuseFailAlloc_274_, 5, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(lean_object* v_pu_276_, lean_object* v_lctx_277_, lean_object* v_funDecl_278_){
_start:
{
uint8_t v_pu_boxed_279_; lean_object* v_res_280_; 
v_pu_boxed_279_ = lean_unbox(v_pu_276_);
v_res_280_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_boxed_279_, v_lctx_277_, v_funDecl_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
return v_x_282_;
}
else
{
lean_object* v_key_283_; lean_object* v_value_284_; lean_object* v_tail_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_294_; 
v_key_283_ = lean_ctor_get(v_x_282_, 0);
v_value_284_ = lean_ctor_get(v_x_282_, 1);
v_tail_285_ = lean_ctor_get(v_x_282_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_294_ == 0)
{
v___x_287_ = v_x_282_;
v_isShared_288_ = v_isSharedCheck_294_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_tail_285_);
lean_inc(v_value_284_);
lean_inc(v_key_283_);
lean_dec(v_x_282_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_294_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v___x_289_; 
v___x_289_ = l_Lean_instBEqFVarId_beq(v_key_283_, v_a_281_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_281_, v_tail_285_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 2, v___x_290_);
v___x_292_ = v___x_287_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_key_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_value_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_del_object(v___x_287_);
lean_dec(v_value_284_);
lean_dec(v_key_283_);
return v_tail_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_295_, v_x_296_);
lean_dec(v_a_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_size_300_; lean_object* v_buckets_301_; lean_object* v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v_fold_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; lean_object* v_bkt_315_; uint8_t v___x_316_; 
v_size_300_ = lean_ctor_get(v_m_298_, 0);
v_buckets_301_ = lean_ctor_get(v_m_298_, 1);
v___x_302_ = lean_array_get_size(v_buckets_301_);
v___x_303_ = l_Lean_instHashableFVarId_hash(v_a_299_);
v___x_304_ = 32ULL;
v___x_305_ = lean_uint64_shift_right(v___x_303_, v___x_304_);
v_fold_306_ = lean_uint64_xor(v___x_303_, v___x_305_);
v___x_307_ = 16ULL;
v___x_308_ = lean_uint64_shift_right(v_fold_306_, v___x_307_);
v___x_309_ = lean_uint64_xor(v_fold_306_, v___x_308_);
v___x_310_ = lean_uint64_to_usize(v___x_309_);
v___x_311_ = lean_usize_of_nat(v___x_302_);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_sub(v___x_311_, v___x_312_);
v___x_314_ = lean_usize_land(v___x_310_, v___x_313_);
v_bkt_315_ = lean_array_uget_borrowed(v_buckets_301_, v___x_314_);
v___x_316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_299_, v_bkt_315_);
if (v___x_316_ == 0)
{
return v_m_298_;
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_329_; 
lean_inc(v_bkt_315_);
lean_inc_ref(v_buckets_301_);
lean_inc(v_size_300_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_m_298_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_330_ = lean_ctor_get(v_m_298_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_m_298_, 0);
lean_dec(v_unused_331_);
v___x_318_ = v_m_298_;
v_isShared_319_ = v_isSharedCheck_329_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_m_298_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_329_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v_buckets_x27_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_320_ = lean_box(0);
v_buckets_x27_321_ = lean_array_uset(v_buckets_301_, v___x_314_, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_sub(v_size_300_, v___x_322_);
lean_dec(v_size_300_);
v___x_324_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_299_, v_bkt_315_);
v___x_325_ = lean_array_uset(v_buckets_x27_321_, v___x_314_, v___x_324_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_325_);
lean_ctor_set(v___x_318_, 0, v___x_323_);
v___x_327_ = v___x_318_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(lean_object* v_m_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_332_, v_a_333_);
lean_dec(v_a_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t v_pu_335_, lean_object* v_lctx_336_, lean_object* v_param_337_){
_start:
{
if (v_pu_335_ == 0)
{
lean_object* v_paramsPure_338_; lean_object* v_paramsImpure_339_; lean_object* v_letDeclsPure_340_; lean_object* v_letDeclsImpure_341_; lean_object* v_funDeclsPure_342_; lean_object* v_funDeclsImpure_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_352_; 
v_paramsPure_338_ = lean_ctor_get(v_lctx_336_, 0);
v_paramsImpure_339_ = lean_ctor_get(v_lctx_336_, 1);
v_letDeclsPure_340_ = lean_ctor_get(v_lctx_336_, 2);
v_letDeclsImpure_341_ = lean_ctor_get(v_lctx_336_, 3);
v_funDeclsPure_342_ = lean_ctor_get(v_lctx_336_, 4);
v_funDeclsImpure_343_ = lean_ctor_get(v_lctx_336_, 5);
v_isSharedCheck_352_ = !lean_is_exclusive(v_lctx_336_);
if (v_isSharedCheck_352_ == 0)
{
v___x_345_ = v_lctx_336_;
v_isShared_346_ = v_isSharedCheck_352_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_funDeclsImpure_343_);
lean_inc(v_funDeclsPure_342_);
lean_inc(v_letDeclsImpure_341_);
lean_inc(v_letDeclsPure_340_);
lean_inc(v_paramsImpure_339_);
lean_inc(v_paramsPure_338_);
lean_dec(v_lctx_336_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_352_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_fvarId_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v_fvarId_347_ = lean_ctor_get(v_param_337_, 0);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsPure_338_, v_fvarId_347_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_348_);
v___x_350_ = v___x_345_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_paramsImpure_339_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_letDeclsPure_340_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_letDeclsImpure_341_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_funDeclsPure_342_);
lean_ctor_set(v_reuseFailAlloc_351_, 5, v_funDeclsImpure_343_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_paramsPure_353_; lean_object* v_paramsImpure_354_; lean_object* v_letDeclsPure_355_; lean_object* v_letDeclsImpure_356_; lean_object* v_funDeclsPure_357_; lean_object* v_funDeclsImpure_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_367_; 
v_paramsPure_353_ = lean_ctor_get(v_lctx_336_, 0);
v_paramsImpure_354_ = lean_ctor_get(v_lctx_336_, 1);
v_letDeclsPure_355_ = lean_ctor_get(v_lctx_336_, 2);
v_letDeclsImpure_356_ = lean_ctor_get(v_lctx_336_, 3);
v_funDeclsPure_357_ = lean_ctor_get(v_lctx_336_, 4);
v_funDeclsImpure_358_ = lean_ctor_get(v_lctx_336_, 5);
v_isSharedCheck_367_ = !lean_is_exclusive(v_lctx_336_);
if (v_isSharedCheck_367_ == 0)
{
v___x_360_ = v_lctx_336_;
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_funDeclsImpure_358_);
lean_inc(v_funDeclsPure_357_);
lean_inc(v_letDeclsImpure_356_);
lean_inc(v_letDeclsPure_355_);
lean_inc(v_paramsImpure_354_);
lean_inc(v_paramsPure_353_);
lean_dec(v_lctx_336_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_fvarId_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_fvarId_362_ = lean_ctor_get(v_param_337_, 0);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsImpure_354_, v_fvarId_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_paramsPure_353_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_letDeclsPure_355_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_letDeclsImpure_356_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_funDeclsPure_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_funDeclsImpure_358_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(lean_object* v_pu_368_, lean_object* v_lctx_369_, lean_object* v_param_370_){
_start:
{
uint8_t v_pu_boxed_371_; lean_object* v_res_372_; 
v_pu_boxed_371_ = lean_unbox(v_pu_368_);
v_res_372_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_boxed_371_, v_lctx_369_, v_param_370_);
lean_dec_ref(v_param_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(lean_object* v_00_u03b2_373_, lean_object* v_m_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_374_, v_a_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(lean_object* v_00_u03b2_377_, lean_object* v_m_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(v_00_u03b2_377_, v_m_378_, v_a_379_);
lean_dec(v_a_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(lean_object* v_00_u03b2_381_, lean_object* v_a_382_, lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_382_, v_x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_385_, lean_object* v_a_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(v_00_u03b2_385_, v_a_386_, v_x_387_);
lean_dec(v_a_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(lean_object* v_as_389_, size_t v_i_390_, size_t v_stop_391_, lean_object* v_b_392_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = lean_usize_dec_eq(v_i_390_, v_stop_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v_fvarId_395_; lean_object* v___x_396_; size_t v___x_397_; size_t v___x_398_; 
v___x_394_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v_fvarId_395_ = lean_ctor_get(v___x_394_, 0);
v___x_396_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_b_392_, v_fvarId_395_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_390_, v___x_397_);
v_i_390_ = v___x_398_;
v_b_392_ = v___x_396_;
goto _start;
}
else
{
return v_b_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0___boxed(lean_object* v_as_400_, lean_object* v_i_401_, lean_object* v_stop_402_, lean_object* v_b_403_){
_start:
{
size_t v_i_boxed_404_; size_t v_stop_boxed_405_; lean_object* v_res_406_; 
v_i_boxed_404_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_stop_boxed_405_ = lean_unbox_usize(v_stop_402_);
lean_dec(v_stop_402_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_as_400_, v_i_boxed_404_, v_stop_boxed_405_, v_b_403_);
lean_dec_ref(v_as_400_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t v_pu_407_, lean_object* v_lctx_408_, lean_object* v_ps_409_){
_start:
{
if (v_pu_407_ == 0)
{
lean_object* v_paramsPure_410_; lean_object* v_paramsImpure_411_; lean_object* v_letDeclsPure_412_; lean_object* v_letDeclsImpure_413_; lean_object* v_funDeclsPure_414_; lean_object* v_funDeclsImpure_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_paramsPure_410_ = lean_ctor_get(v_lctx_408_, 0);
v_paramsImpure_411_ = lean_ctor_get(v_lctx_408_, 1);
v_letDeclsPure_412_ = lean_ctor_get(v_lctx_408_, 2);
v_letDeclsImpure_413_ = lean_ctor_get(v_lctx_408_, 3);
v_funDeclsPure_414_ = lean_ctor_get(v_lctx_408_, 4);
v_funDeclsImpure_415_ = lean_ctor_get(v_lctx_408_, 5);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_array_get_size(v_ps_409_);
v___x_418_ = lean_nat_dec_lt(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
return v_lctx_408_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_le(v___x_417_, v___x_417_);
if (v___x_419_ == 0)
{
if (v___x_418_ == 0)
{
return v_lctx_408_;
}
else
{
lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
lean_inc_ref(v_funDeclsImpure_415_);
lean_inc_ref(v_funDeclsPure_414_);
lean_inc_ref(v_letDeclsImpure_413_);
lean_inc_ref(v_letDeclsPure_412_);
lean_inc_ref(v_paramsImpure_411_);
lean_inc_ref(v_paramsPure_410_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_lctx_408_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_430_ = lean_ctor_get(v_lctx_408_, 5);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_lctx_408_, 4);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_lctx_408_, 3);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_lctx_408_, 2);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_lctx_408_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_lctx_408_, 0);
lean_dec(v_unused_435_);
v___x_421_ = v_lctx_408_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_dec(v_lctx_408_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_423_ = ((size_t)0ULL);
v___x_424_ = lean_usize_of_nat(v___x_417_);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_409_, v___x_423_, v___x_424_, v_paramsPure_410_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_paramsImpure_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_letDeclsPure_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_letDeclsImpure_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_funDeclsPure_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_funDeclsImpure_415_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
lean_inc_ref(v_funDeclsImpure_415_);
lean_inc_ref(v_funDeclsPure_414_);
lean_inc_ref(v_letDeclsImpure_413_);
lean_inc_ref(v_letDeclsPure_412_);
lean_inc_ref(v_paramsImpure_411_);
lean_inc_ref(v_paramsPure_410_);
v_isSharedCheck_445_ = !lean_is_exclusive(v_lctx_408_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_446_ = lean_ctor_get(v_lctx_408_, 5);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_lctx_408_, 4);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_lctx_408_, 3);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_lctx_408_, 2);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_lctx_408_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_lctx_408_, 0);
lean_dec(v_unused_451_);
v___x_437_ = v_lctx_408_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_lctx_408_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_417_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_409_, v___x_439_, v___x_440_, v_paramsPure_410_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_441_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_paramsImpure_411_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_letDeclsPure_412_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_letDeclsImpure_413_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_funDeclsPure_414_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_funDeclsImpure_415_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v_paramsPure_452_; lean_object* v_paramsImpure_453_; lean_object* v_letDeclsPure_454_; lean_object* v_letDeclsImpure_455_; lean_object* v_funDeclsPure_456_; lean_object* v_funDeclsImpure_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_paramsPure_452_ = lean_ctor_get(v_lctx_408_, 0);
v_paramsImpure_453_ = lean_ctor_get(v_lctx_408_, 1);
v_letDeclsPure_454_ = lean_ctor_get(v_lctx_408_, 2);
v_letDeclsImpure_455_ = lean_ctor_get(v_lctx_408_, 3);
v_funDeclsPure_456_ = lean_ctor_get(v_lctx_408_, 4);
v_funDeclsImpure_457_ = lean_ctor_get(v_lctx_408_, 5);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_array_get_size(v_ps_409_);
v___x_460_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
return v_lctx_408_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = lean_nat_dec_le(v___x_459_, v___x_459_);
if (v___x_461_ == 0)
{
if (v___x_460_ == 0)
{
return v_lctx_408_;
}
else
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_471_; 
lean_inc_ref(v_funDeclsImpure_457_);
lean_inc_ref(v_funDeclsPure_456_);
lean_inc_ref(v_letDeclsImpure_455_);
lean_inc_ref(v_letDeclsPure_454_);
lean_inc_ref(v_paramsImpure_453_);
lean_inc_ref(v_paramsPure_452_);
v_isSharedCheck_471_ = !lean_is_exclusive(v_lctx_408_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_472_ = lean_ctor_get(v_lctx_408_, 5);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_lctx_408_, 4);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_lctx_408_, 3);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_lctx_408_, 2);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_lctx_408_, 1);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_lctx_408_, 0);
lean_dec(v_unused_477_);
v___x_463_ = v_lctx_408_;
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_lctx_408_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_465_ = ((size_t)0ULL);
v___x_466_ = lean_usize_of_nat(v___x_459_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_409_, v___x_465_, v___x_466_, v_paramsImpure_453_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_467_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_paramsPure_452_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_letDeclsPure_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_letDeclsImpure_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_funDeclsPure_456_);
lean_ctor_set(v_reuseFailAlloc_470_, 5, v_funDeclsImpure_457_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
lean_inc_ref(v_funDeclsImpure_457_);
lean_inc_ref(v_funDeclsPure_456_);
lean_inc_ref(v_letDeclsImpure_455_);
lean_inc_ref(v_letDeclsPure_454_);
lean_inc_ref(v_paramsImpure_453_);
lean_inc_ref(v_paramsPure_452_);
v_isSharedCheck_487_ = !lean_is_exclusive(v_lctx_408_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; lean_object* v_unused_490_; lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_488_ = lean_ctor_get(v_lctx_408_, 5);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_lctx_408_, 4);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_lctx_408_, 3);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_lctx_408_, 2);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_lctx_408_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_lctx_408_, 0);
lean_dec(v_unused_493_);
v___x_479_ = v_lctx_408_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_dec(v_lctx_408_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_459_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_409_, v___x_481_, v___x_482_, v_paramsImpure_453_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_483_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_paramsPure_452_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_letDeclsPure_454_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_letDeclsImpure_455_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_funDeclsPure_456_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_funDeclsImpure_457_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(lean_object* v_pu_494_, lean_object* v_lctx_495_, lean_object* v_ps_496_){
_start:
{
uint8_t v_pu_boxed_497_; lean_object* v_res_498_; 
v_pu_boxed_497_ = lean_unbox(v_pu_494_);
v_res_498_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_boxed_497_, v_lctx_495_, v_ps_496_);
lean_dec_ref(v_ps_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t v_pu_499_, lean_object* v_lctx_500_, lean_object* v_decl_501_){
_start:
{
if (v_pu_499_ == 0)
{
lean_object* v_paramsPure_502_; lean_object* v_paramsImpure_503_; lean_object* v_letDeclsPure_504_; lean_object* v_letDeclsImpure_505_; lean_object* v_funDeclsPure_506_; lean_object* v_funDeclsImpure_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_516_; 
v_paramsPure_502_ = lean_ctor_get(v_lctx_500_, 0);
v_paramsImpure_503_ = lean_ctor_get(v_lctx_500_, 1);
v_letDeclsPure_504_ = lean_ctor_get(v_lctx_500_, 2);
v_letDeclsImpure_505_ = lean_ctor_get(v_lctx_500_, 3);
v_funDeclsPure_506_ = lean_ctor_get(v_lctx_500_, 4);
v_funDeclsImpure_507_ = lean_ctor_get(v_lctx_500_, 5);
v_isSharedCheck_516_ = !lean_is_exclusive(v_lctx_500_);
if (v_isSharedCheck_516_ == 0)
{
v___x_509_ = v_lctx_500_;
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_funDeclsImpure_507_);
lean_inc(v_funDeclsPure_506_);
lean_inc(v_letDeclsImpure_505_);
lean_inc(v_letDeclsPure_504_);
lean_inc(v_paramsImpure_503_);
lean_inc(v_paramsPure_502_);
lean_dec(v_lctx_500_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_fvarId_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v_fvarId_511_ = lean_ctor_get(v_decl_501_, 0);
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsPure_504_, v_fvarId_511_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 2, v___x_512_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_paramsPure_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_paramsImpure_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_letDeclsImpure_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_funDeclsPure_506_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_funDeclsImpure_507_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_paramsPure_517_; lean_object* v_paramsImpure_518_; lean_object* v_letDeclsPure_519_; lean_object* v_letDeclsImpure_520_; lean_object* v_funDeclsPure_521_; lean_object* v_funDeclsImpure_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_paramsPure_517_ = lean_ctor_get(v_lctx_500_, 0);
v_paramsImpure_518_ = lean_ctor_get(v_lctx_500_, 1);
v_letDeclsPure_519_ = lean_ctor_get(v_lctx_500_, 2);
v_letDeclsImpure_520_ = lean_ctor_get(v_lctx_500_, 3);
v_funDeclsPure_521_ = lean_ctor_get(v_lctx_500_, 4);
v_funDeclsImpure_522_ = lean_ctor_get(v_lctx_500_, 5);
v_isSharedCheck_531_ = !lean_is_exclusive(v_lctx_500_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v_lctx_500_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_funDeclsImpure_522_);
lean_inc(v_funDeclsPure_521_);
lean_inc(v_letDeclsImpure_520_);
lean_inc(v_letDeclsPure_519_);
lean_inc(v_paramsImpure_518_);
lean_inc(v_paramsPure_517_);
lean_dec(v_lctx_500_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_fvarId_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v_fvarId_526_ = lean_ctor_get(v_decl_501_, 0);
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsImpure_520_, v_fvarId_526_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v___x_527_);
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_paramsPure_517_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_paramsImpure_518_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_letDeclsPure_519_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v_funDeclsPure_521_);
lean_ctor_set(v_reuseFailAlloc_530_, 5, v_funDeclsImpure_522_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(lean_object* v_pu_532_, lean_object* v_lctx_533_, lean_object* v_decl_534_){
_start:
{
uint8_t v_pu_boxed_535_; lean_object* v_res_536_; 
v_pu_boxed_535_ = lean_unbox(v_pu_532_);
v_res_536_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_boxed_535_, v_lctx_533_, v_decl_534_);
lean_dec_ref(v_decl_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t v_pu_537_, lean_object* v_lctx_538_, lean_object* v_decl_539_, uint8_t v_recursive_540_){
_start:
{
lean_object* v___y_542_; 
if (v_pu_537_ == 0)
{
lean_object* v_fvarId_547_; lean_object* v_paramsPure_548_; lean_object* v_paramsImpure_549_; lean_object* v_letDeclsPure_550_; lean_object* v_letDeclsImpure_551_; lean_object* v_funDeclsPure_552_; lean_object* v_funDeclsImpure_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_561_; 
v_fvarId_547_ = lean_ctor_get(v_decl_539_, 0);
v_paramsPure_548_ = lean_ctor_get(v_lctx_538_, 0);
v_paramsImpure_549_ = lean_ctor_get(v_lctx_538_, 1);
v_letDeclsPure_550_ = lean_ctor_get(v_lctx_538_, 2);
v_letDeclsImpure_551_ = lean_ctor_get(v_lctx_538_, 3);
v_funDeclsPure_552_ = lean_ctor_get(v_lctx_538_, 4);
v_funDeclsImpure_553_ = lean_ctor_get(v_lctx_538_, 5);
v_isSharedCheck_561_ = !lean_is_exclusive(v_lctx_538_);
if (v_isSharedCheck_561_ == 0)
{
v___x_555_ = v_lctx_538_;
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_funDeclsImpure_553_);
lean_inc(v_funDeclsPure_552_);
lean_inc(v_letDeclsImpure_551_);
lean_inc(v_letDeclsPure_550_);
lean_inc(v_paramsImpure_549_);
lean_inc(v_paramsPure_548_);
lean_dec(v_lctx_538_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsPure_552_, v_fvarId_547_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 4, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_paramsPure_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_paramsImpure_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_letDeclsPure_550_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_letDeclsImpure_551_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_funDeclsImpure_553_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
v___y_542_ = v___x_559_;
goto v___jp_541_;
}
}
}
else
{
lean_object* v_fvarId_562_; lean_object* v_paramsPure_563_; lean_object* v_paramsImpure_564_; lean_object* v_letDeclsPure_565_; lean_object* v_letDeclsImpure_566_; lean_object* v_funDeclsPure_567_; lean_object* v_funDeclsImpure_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_fvarId_562_ = lean_ctor_get(v_decl_539_, 0);
v_paramsPure_563_ = lean_ctor_get(v_lctx_538_, 0);
v_paramsImpure_564_ = lean_ctor_get(v_lctx_538_, 1);
v_letDeclsPure_565_ = lean_ctor_get(v_lctx_538_, 2);
v_letDeclsImpure_566_ = lean_ctor_get(v_lctx_538_, 3);
v_funDeclsPure_567_ = lean_ctor_get(v_lctx_538_, 4);
v_funDeclsImpure_568_ = lean_ctor_get(v_lctx_538_, 5);
v_isSharedCheck_576_ = !lean_is_exclusive(v_lctx_538_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v_lctx_538_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_funDeclsImpure_568_);
lean_inc(v_funDeclsPure_567_);
lean_inc(v_letDeclsImpure_566_);
lean_inc(v_letDeclsPure_565_);
lean_inc(v_paramsImpure_564_);
lean_inc(v_paramsPure_563_);
lean_dec(v_lctx_538_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsImpure_568_, v_fvarId_562_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 5, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_paramsPure_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_paramsImpure_564_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_letDeclsPure_565_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_letDeclsImpure_566_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_funDeclsPure_567_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v___y_542_ = v___x_574_;
goto v___jp_541_;
}
}
}
v___jp_541_:
{
if (v_recursive_540_ == 0)
{
return v___y_542_;
}
else
{
lean_object* v_params_543_; lean_object* v_value_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_params_543_ = lean_ctor_get(v_decl_539_, 2);
v_value_544_ = lean_ctor_get(v_decl_539_, 4);
v___x_545_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_537_, v___y_542_, v_params_543_);
v___x_546_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_537_, v_value_544_, v___x_545_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t v_pu_577_, lean_object* v_code_578_, lean_object* v_lctx_579_){
_start:
{
switch(lean_obj_tag(v_code_578_))
{
case 0:
{
lean_object* v_decl_580_; lean_object* v_k_581_; lean_object* v___x_582_; 
v_decl_580_ = lean_ctor_get(v_code_578_, 0);
v_k_581_ = lean_ctor_get(v_code_578_, 1);
v___x_582_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_577_, v_lctx_579_, v_decl_580_);
v_code_578_ = v_k_581_;
v_lctx_579_ = v___x_582_;
goto _start;
}
case 1:
{
lean_object* v_decl_584_; lean_object* v_k_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v_decl_584_ = lean_ctor_get(v_code_578_, 0);
v_k_585_ = lean_ctor_get(v_code_578_, 1);
v___x_586_ = 1;
v___x_587_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_577_, v_lctx_579_, v_decl_584_, v___x_586_);
v_code_578_ = v_k_585_;
v_lctx_579_ = v___x_587_;
goto _start;
}
case 2:
{
lean_object* v_decl_589_; lean_object* v_k_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v_decl_589_ = lean_ctor_get(v_code_578_, 0);
v_k_590_ = lean_ctor_get(v_code_578_, 1);
v___x_591_ = 1;
v___x_592_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_577_, v_lctx_579_, v_decl_589_, v___x_591_);
v_code_578_ = v_k_590_;
v_lctx_579_ = v___x_592_;
goto _start;
}
case 4:
{
lean_object* v_cases_594_; lean_object* v_alts_595_; lean_object* v___x_596_; 
v_cases_594_ = lean_ctor_get(v_code_578_, 0);
v_alts_595_ = lean_ctor_get(v_cases_594_, 3);
v___x_596_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_577_, v_alts_595_, v_lctx_579_);
return v___x_596_;
}
case 7:
{
lean_object* v_k_597_; 
v_k_597_ = lean_ctor_get(v_code_578_, 3);
v_code_578_ = v_k_597_;
goto _start;
}
case 8:
{
lean_object* v_k_599_; 
v_k_599_ = lean_ctor_get(v_code_578_, 3);
v_code_578_ = v_k_599_;
goto _start;
}
case 9:
{
lean_object* v_k_601_; 
v_k_601_ = lean_ctor_get(v_code_578_, 5);
v_code_578_ = v_k_601_;
goto _start;
}
case 10:
{
lean_object* v_k_603_; 
v_k_603_ = lean_ctor_get(v_code_578_, 2);
v_code_578_ = v_k_603_;
goto _start;
}
case 11:
{
lean_object* v_k_605_; 
v_k_605_ = lean_ctor_get(v_code_578_, 2);
v_code_578_ = v_k_605_;
goto _start;
}
case 12:
{
lean_object* v_k_607_; 
v_k_607_ = lean_ctor_get(v_code_578_, 2);
v_code_578_ = v_k_607_;
goto _start;
}
case 13:
{
lean_object* v_k_609_; 
v_k_609_ = lean_ctor_get(v_code_578_, 1);
v_code_578_ = v_k_609_;
goto _start;
}
default: 
{
return v_lctx_579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(uint8_t v_pu_611_, lean_object* v_as_612_, size_t v_i_613_, size_t v_stop_614_, lean_object* v_b_615_){
_start:
{
lean_object* v___y_617_; uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_613_, v_stop_614_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_array_uget_borrowed(v_as_612_, v_i_613_);
switch(lean_obj_tag(v___x_622_))
{
case 0:
{
lean_object* v_params_623_; lean_object* v_code_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_params_623_ = lean_ctor_get(v___x_622_, 1);
v_code_624_ = lean_ctor_get(v___x_622_, 2);
v___x_625_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_611_, v_b_615_, v_params_623_);
v___x_626_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_611_, v_code_624_, v___x_625_);
v___y_617_ = v___x_626_;
goto v___jp_616_;
}
case 1:
{
lean_object* v_code_627_; lean_object* v___x_628_; 
v_code_627_ = lean_ctor_get(v___x_622_, 1);
v___x_628_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_611_, v_code_627_, v_b_615_);
v___y_617_ = v___x_628_;
goto v___jp_616_;
}
default: 
{
lean_object* v_code_629_; lean_object* v___x_630_; 
v_code_629_ = lean_ctor_get(v___x_622_, 0);
v___x_630_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_611_, v_code_629_, v_b_615_);
v___y_617_ = v___x_630_;
goto v___jp_616_;
}
}
}
else
{
return v_b_615_;
}
v___jp_616_:
{
size_t v___x_618_; size_t v___x_619_; 
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_add(v_i_613_, v___x_618_);
v_i_613_ = v___x_619_;
v_b_615_ = v___y_617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts(uint8_t v_pu_631_, lean_object* v_alts_632_, lean_object* v_lctx_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_array_get_size(v_alts_632_);
v___x_636_ = lean_nat_dec_lt(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
return v_lctx_633_;
}
else
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_637_ == 0)
{
if (v___x_636_ == 0)
{
return v_lctx_633_;
}
else
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_usize_of_nat(v___x_635_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_631_, v_alts_632_, v___x_638_, v___x_639_, v_lctx_633_);
return v___x_640_;
}
}
else
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_635_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_631_, v_alts_632_, v___x_641_, v___x_642_, v_lctx_633_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(lean_object* v_pu_644_, lean_object* v_alts_645_, lean_object* v_lctx_646_){
_start:
{
uint8_t v_pu_boxed_647_; lean_object* v_res_648_; 
v_pu_boxed_647_ = lean_unbox(v_pu_644_);
v_res_648_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_boxed_647_, v_alts_645_, v_lctx_646_);
lean_dec_ref(v_alts_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(lean_object* v_pu_649_, lean_object* v_as_650_, lean_object* v_i_651_, lean_object* v_stop_652_, lean_object* v_b_653_){
_start:
{
uint8_t v_pu_boxed_654_; size_t v_i_boxed_655_; size_t v_stop_boxed_656_; lean_object* v_res_657_; 
v_pu_boxed_654_ = lean_unbox(v_pu_649_);
v_i_boxed_655_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_stop_boxed_656_ = lean_unbox_usize(v_stop_652_);
lean_dec(v_stop_652_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_boxed_654_, v_as_650_, v_i_boxed_655_, v_stop_boxed_656_, v_b_653_);
lean_dec_ref(v_as_650_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(lean_object* v_pu_658_, lean_object* v_lctx_659_, lean_object* v_decl_660_, lean_object* v_recursive_661_){
_start:
{
uint8_t v_pu_boxed_662_; uint8_t v_recursive_boxed_663_; lean_object* v_res_664_; 
v_pu_boxed_662_ = lean_unbox(v_pu_658_);
v_recursive_boxed_663_ = lean_unbox(v_recursive_661_);
v_res_664_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_boxed_662_, v_lctx_659_, v_decl_660_, v_recursive_boxed_663_);
lean_dec_ref(v_decl_660_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(lean_object* v_pu_665_, lean_object* v_code_666_, lean_object* v_lctx_667_){
_start:
{
uint8_t v_pu_boxed_668_; lean_object* v_res_669_; 
v_pu_boxed_668_ = lean_unbox(v_pu_665_);
v_res_669_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_boxed_668_, v_code_666_, v_lctx_667_);
lean_dec_ref(v_code_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params(lean_object* v_lctx_670_, uint8_t v_pu_671_){
_start:
{
if (v_pu_671_ == 0)
{
lean_object* v_paramsPure_672_; 
v_paramsPure_672_ = lean_ctor_get(v_lctx_670_, 0);
lean_inc_ref(v_paramsPure_672_);
return v_paramsPure_672_;
}
else
{
lean_object* v_paramsImpure_673_; 
v_paramsImpure_673_ = lean_ctor_get(v_lctx_670_, 1);
lean_inc_ref(v_paramsImpure_673_);
return v_paramsImpure_673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params___boxed(lean_object* v_lctx_674_, lean_object* v_pu_675_){
_start:
{
uint8_t v_pu_boxed_676_; lean_object* v_res_677_; 
v_pu_boxed_676_ = lean_unbox(v_pu_675_);
v_res_677_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_674_, v_pu_boxed_676_);
lean_dec_ref(v_lctx_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls(lean_object* v_lctx_678_, uint8_t v_pu_679_){
_start:
{
if (v_pu_679_ == 0)
{
lean_object* v_letDeclsPure_680_; 
v_letDeclsPure_680_ = lean_ctor_get(v_lctx_678_, 2);
lean_inc_ref(v_letDeclsPure_680_);
return v_letDeclsPure_680_;
}
else
{
lean_object* v_letDeclsImpure_681_; 
v_letDeclsImpure_681_ = lean_ctor_get(v_lctx_678_, 3);
lean_inc_ref(v_letDeclsImpure_681_);
return v_letDeclsImpure_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(lean_object* v_lctx_682_, lean_object* v_pu_683_){
_start:
{
uint8_t v_pu_boxed_684_; lean_object* v_res_685_; 
v_pu_boxed_684_ = lean_unbox(v_pu_683_);
v_res_685_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_682_, v_pu_boxed_684_);
lean_dec_ref(v_lctx_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls(lean_object* v_lctx_686_, uint8_t v_pu_687_){
_start:
{
if (v_pu_687_ == 0)
{
lean_object* v_funDeclsPure_688_; 
v_funDeclsPure_688_ = lean_ctor_get(v_lctx_686_, 4);
lean_inc_ref(v_funDeclsPure_688_);
return v_funDeclsPure_688_;
}
else
{
lean_object* v_funDeclsImpure_689_; 
v_funDeclsImpure_689_ = lean_ctor_get(v_lctx_686_, 5);
lean_inc_ref(v_funDeclsImpure_689_);
return v_funDeclsImpure_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(lean_object* v_lctx_690_, lean_object* v_pu_691_){
_start:
{
uint8_t v_pu_boxed_692_; lean_object* v_res_693_; 
v_pu_boxed_692_ = lean_unbox(v_pu_691_);
v_res_693_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_690_, v_pu_boxed_692_);
lean_dec_ref(v_lctx_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
if (lean_obj_tag(v_a_694_) == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_a_695_);
return v___x_696_;
}
else
{
lean_object* v_value_697_; lean_object* v_tail_698_; lean_object* v_fvarId_699_; lean_object* v_binderName_700_; lean_object* v_type_701_; lean_object* v___x_702_; uint8_t v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_value_697_ = lean_ctor_get(v_a_694_, 1);
v_tail_698_ = lean_ctor_get(v_a_694_, 2);
v_fvarId_699_ = lean_ctor_get(v_value_697_, 0);
v_binderName_700_ = lean_ctor_get(v_value_697_, 1);
v_type_701_ = lean_ctor_get(v_value_697_, 3);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = 0;
v___x_704_ = 0;
lean_inc_ref(v_type_701_);
lean_inc(v_binderName_700_);
lean_inc(v_fvarId_699_);
v___x_705_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_705_, 0, v___x_702_);
lean_ctor_set(v___x_705_, 1, v_fvarId_699_);
lean_ctor_set(v___x_705_, 2, v_binderName_700_);
lean_ctor_set(v___x_705_, 3, v_type_701_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*4, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*4 + 1, v___x_704_);
v___x_706_ = l_Lean_LocalContext_addDecl(v_a_695_, v___x_705_);
v_a_694_ = v_tail_698_;
v_a_695_ = v___x_706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_708_, v_a_709_);
lean_dec(v_a_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_715_ == 0)
{
return v_b_714_;
}
else
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_array_uget_borrowed(v_as_711_, v_i_713_);
v___x_717_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_716_, v_b_714_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
return v_a_718_;
}
else
{
lean_object* v_a_719_; size_t v___x_720_; size_t v___x_721_; 
v_a_719_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_717_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_713_, v___x_720_);
v_i_713_ = v___x_721_;
v_b_714_ = v_a_719_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5___boxed(lean_object* v_as_723_, lean_object* v_sz_724_, lean_object* v_i_725_, lean_object* v_b_726_){
_start:
{
size_t v_sz_boxed_727_; size_t v_i_boxed_728_; lean_object* v_res_729_; 
v_sz_boxed_727_ = lean_unbox_usize(v_sz_724_);
lean_dec(v_sz_724_);
v_i_boxed_728_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_as_723_, v_sz_boxed_727_, v_i_boxed_728_, v_b_726_);
lean_dec_ref(v_as_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(uint8_t v_pu_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v_a_732_);
return v___x_733_;
}
else
{
lean_object* v_value_734_; lean_object* v_tail_735_; lean_object* v_fvarId_736_; lean_object* v_binderName_737_; lean_object* v_type_738_; lean_object* v_value_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_value_734_ = lean_ctor_get(v_a_731_, 1);
lean_inc(v_value_734_);
v_tail_735_ = lean_ctor_get(v_a_731_, 2);
lean_inc(v_tail_735_);
lean_dec_ref(v_a_731_);
v_fvarId_736_ = lean_ctor_get(v_value_734_, 0);
lean_inc(v_fvarId_736_);
v_binderName_737_ = lean_ctor_get(v_value_734_, 1);
lean_inc(v_binderName_737_);
v_type_738_ = lean_ctor_get(v_value_734_, 2);
lean_inc_ref(v_type_738_);
v_value_739_ = lean_ctor_get(v_value_734_, 3);
lean_inc(v_value_739_);
lean_dec(v_value_734_);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_730_, v_value_739_);
v___x_742_ = 1;
v___x_743_ = 0;
v___x_744_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_744_, 0, v___x_740_);
lean_ctor_set(v___x_744_, 1, v_fvarId_736_);
lean_ctor_set(v___x_744_, 2, v_binderName_737_);
lean_ctor_set(v___x_744_, 3, v_type_738_);
lean_ctor_set(v___x_744_, 4, v___x_741_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*5, v___x_742_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*5 + 1, v___x_743_);
v___x_745_ = l_Lean_LocalContext_addDecl(v_a_732_, v___x_744_);
v_a_731_ = v_tail_735_;
v_a_732_ = v___x_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object* v_pu_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
uint8_t v_pu_boxed_750_; lean_object* v_res_751_; 
v_pu_boxed_750_ = lean_unbox(v_pu_747_);
v_res_751_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_boxed_750_, v_a_748_, v_a_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(uint8_t v_pu_752_, lean_object* v_as_753_, size_t v_sz_754_, size_t v_i_755_, lean_object* v_b_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_lt(v_i_755_, v_sz_754_);
if (v___x_757_ == 0)
{
return v_b_756_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_array_uget_borrowed(v_as_753_, v_i_755_);
lean_inc(v_a_758_);
v___x_759_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_752_, v_a_758_, v_b_756_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
return v_a_760_;
}
else
{
lean_object* v_a_761_; size_t v___x_762_; size_t v___x_763_; 
v_a_761_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_761_);
lean_dec_ref(v___x_759_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_755_, v___x_762_);
v_i_755_ = v___x_763_;
v_b_756_ = v_a_761_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4___boxed(lean_object* v_pu_765_, lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_b_769_){
_start:
{
uint8_t v_pu_boxed_770_; size_t v_sz_boxed_771_; size_t v_i_boxed_772_; lean_object* v_res_773_; 
v_pu_boxed_770_ = lean_unbox(v_pu_765_);
v_sz_boxed_771_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_772_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_boxed_770_, v_as_766_, v_sz_boxed_771_, v_i_boxed_772_, v_b_769_);
lean_dec_ref(v_as_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
if (lean_obj_tag(v_a_774_) == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_a_775_);
return v___x_776_;
}
else
{
lean_object* v_value_777_; lean_object* v_tail_778_; lean_object* v_fvarId_779_; lean_object* v_binderName_780_; lean_object* v_type_781_; lean_object* v___x_782_; uint8_t v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_value_777_ = lean_ctor_get(v_a_774_, 1);
v_tail_778_ = lean_ctor_get(v_a_774_, 2);
v_fvarId_779_ = lean_ctor_get(v_value_777_, 0);
v_binderName_780_ = lean_ctor_get(v_value_777_, 1);
v_type_781_ = lean_ctor_get(v_value_777_, 2);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = 0;
v___x_784_ = 0;
lean_inc_ref(v_type_781_);
lean_inc(v_binderName_780_);
lean_inc(v_fvarId_779_);
v___x_785_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v_fvarId_779_);
lean_ctor_set(v___x_785_, 2, v_binderName_780_);
lean_ctor_set(v___x_785_, 3, v_type_781_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*4, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*4 + 1, v___x_784_);
v___x_786_ = l_Lean_LocalContext_addDecl(v_a_775_, v___x_785_);
v_a_774_ = v_tail_778_;
v_a_775_ = v___x_786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_788_, v_a_789_);
lean_dec(v_a_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(lean_object* v_as_791_, size_t v_sz_792_, size_t v_i_793_, lean_object* v_b_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_lt(v_i_793_, v_sz_792_);
if (v___x_795_ == 0)
{
return v_b_794_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_array_uget_borrowed(v_as_791_, v_i_793_);
v___x_797_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_796_, v_b_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
return v_a_798_;
}
else
{
lean_object* v_a_799_; size_t v___x_800_; size_t v___x_801_; 
v_a_799_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_797_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_i_793_, v___x_800_);
v_i_793_ = v___x_801_;
v_b_794_ = v_a_799_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3___boxed(lean_object* v_as_803_, lean_object* v_sz_804_, lean_object* v_i_805_, lean_object* v_b_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_804_);
lean_dec(v_sz_804_);
v_i_boxed_808_ = lean_unbox_usize(v_i_805_);
lean_dec(v_i_805_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_as_803_, v_sz_boxed_807_, v_i_boxed_808_, v_b_806_);
lean_dec_ref(v_as_803_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_unsigned_to_nat(32u);
v___x_814_ = lean_mk_empty_array_with_capacity(v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3(void){
_start:
{
size_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_816_ = ((size_t)5ULL);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_unsigned_to_nat(32u);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_818_);
v___x_820_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2);
v___x_821_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
lean_ctor_set(v___x_821_, 2, v___x_817_);
lean_ctor_set(v___x_821_, 3, v___x_817_);
lean_ctor_set_usize(v___x_821_, 4, v___x_816_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_result_825_; 
v___x_822_ = lean_box(1);
v___x_823_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3);
v___x_824_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1);
v_result_825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_825_, 0, v___x_824_);
lean_ctor_set(v_result_825_, 1, v___x_823_);
lean_ctor_set(v_result_825_, 2, v___x_822_);
return v_result_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object* v_lctx_826_, uint8_t v_pu_827_){
_start:
{
size_t v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; size_t v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v_result_844_; lean_object* v___y_846_; 
v_result_844_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4);
if (v_pu_827_ == 0)
{
lean_object* v_paramsPure_853_; 
v_paramsPure_853_ = lean_ctor_get(v_lctx_826_, 0);
v___y_846_ = v_paramsPure_853_;
goto v___jp_845_;
}
else
{
lean_object* v_paramsImpure_854_; 
v_paramsImpure_854_ = lean_ctor_get(v_lctx_826_, 1);
v___y_846_ = v_paramsImpure_854_;
goto v___jp_845_;
}
v___jp_828_:
{
lean_object* v_buckets_832_; size_t v_sz_833_; lean_object* v___x_834_; 
v_buckets_832_ = lean_ctor_get(v___y_831_, 1);
v_sz_833_ = lean_array_size(v_buckets_832_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_buckets_832_, v_sz_833_, v___y_829_, v___y_830_);
return v___x_834_;
}
v___jp_835_:
{
lean_object* v_buckets_839_; size_t v_sz_840_; lean_object* v___x_841_; 
v_buckets_839_ = lean_ctor_get(v___y_838_, 1);
v_sz_840_ = lean_array_size(v_buckets_839_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_827_, v_buckets_839_, v_sz_840_, v___y_836_, v___y_837_);
if (v_pu_827_ == 0)
{
lean_object* v_funDeclsPure_842_; 
v_funDeclsPure_842_ = lean_ctor_get(v_lctx_826_, 4);
v___y_829_ = v___y_836_;
v___y_830_ = v___x_841_;
v___y_831_ = v_funDeclsPure_842_;
goto v___jp_828_;
}
else
{
lean_object* v_funDeclsImpure_843_; 
v_funDeclsImpure_843_ = lean_ctor_get(v_lctx_826_, 5);
v___y_829_ = v___y_836_;
v___y_830_ = v___x_841_;
v___y_831_ = v_funDeclsImpure_843_;
goto v___jp_828_;
}
}
v___jp_845_:
{
lean_object* v_buckets_847_; size_t v_sz_848_; size_t v___x_849_; lean_object* v___x_850_; 
v_buckets_847_ = lean_ctor_get(v___y_846_, 1);
v_sz_848_ = lean_array_size(v_buckets_847_);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_buckets_847_, v_sz_848_, v___x_849_, v_result_844_);
if (v_pu_827_ == 0)
{
lean_object* v_letDeclsPure_851_; 
v_letDeclsPure_851_ = lean_ctor_get(v_lctx_826_, 2);
v___y_836_ = v___x_849_;
v___y_837_ = v___x_850_;
v___y_838_ = v_letDeclsPure_851_;
goto v___jp_835_;
}
else
{
lean_object* v_letDeclsImpure_852_; 
v_letDeclsImpure_852_ = lean_ctor_get(v_lctx_826_, 3);
v___y_836_ = v___x_849_;
v___y_837_ = v___x_850_;
v___y_838_ = v_letDeclsImpure_852_;
goto v___jp_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(lean_object* v_lctx_855_, lean_object* v_pu_856_){
_start:
{
uint8_t v_pu_boxed_857_; lean_object* v_res_858_; 
v_pu_boxed_857_ = lean_unbox(v_pu_856_);
v_res_858_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_855_, v_pu_boxed_857_);
lean_dec_ref(v_lctx_855_);
return v_res_858_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LCtx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
