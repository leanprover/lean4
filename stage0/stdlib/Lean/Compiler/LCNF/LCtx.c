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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
lean_inc_ref(v_funDeclsImpure_416_);
lean_inc_ref(v_funDeclsPure_415_);
lean_inc_ref(v_letDeclsImpure_414_);
lean_inc_ref(v_letDeclsPure_413_);
lean_inc_ref(v_paramsImpure_412_);
lean_inc_ref(v_paramsPure_411_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_lctx_409_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_430_ = lean_ctor_get(v_lctx_409_, 5);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_lctx_409_, 4);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_lctx_409_, 3);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_lctx_409_, 2);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_lctx_409_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_lctx_409_, 0);
lean_dec(v_unused_435_);
v___x_421_ = v_lctx_409_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_dec(v_lctx_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_423_ = ((size_t)0ULL);
v___x_424_ = lean_usize_of_nat(v___x_418_);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_410_, v___x_423_, v___x_424_, v_paramsPure_411_);
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
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_paramsImpure_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_letDeclsPure_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_letDeclsImpure_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_funDeclsPure_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_funDeclsImpure_416_);
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
lean_object* v_paramsPure_436_; lean_object* v_paramsImpure_437_; lean_object* v_letDeclsPure_438_; lean_object* v_letDeclsImpure_439_; lean_object* v_funDeclsPure_440_; lean_object* v_funDeclsImpure_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_paramsPure_436_ = lean_ctor_get(v_lctx_409_, 0);
v_paramsImpure_437_ = lean_ctor_get(v_lctx_409_, 1);
v_letDeclsPure_438_ = lean_ctor_get(v_lctx_409_, 2);
v_letDeclsImpure_439_ = lean_ctor_get(v_lctx_409_, 3);
v_funDeclsPure_440_ = lean_ctor_get(v_lctx_409_, 4);
v_funDeclsImpure_441_ = lean_ctor_get(v_lctx_409_, 5);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_array_get_size(v_ps_410_);
v___x_444_ = lean_nat_dec_lt(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
return v_lctx_409_;
}
else
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_454_; 
lean_inc_ref(v_funDeclsImpure_441_);
lean_inc_ref(v_funDeclsPure_440_);
lean_inc_ref(v_letDeclsImpure_439_);
lean_inc_ref(v_letDeclsPure_438_);
lean_inc_ref(v_paramsImpure_437_);
lean_inc_ref(v_paramsPure_436_);
v_isSharedCheck_454_ = !lean_is_exclusive(v_lctx_409_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_455_ = lean_ctor_get(v_lctx_409_, 5);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_lctx_409_, 4);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_lctx_409_, 3);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_lctx_409_, 2);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_lctx_409_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_lctx_409_, 0);
lean_dec(v_unused_460_);
v___x_446_ = v_lctx_409_;
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_lctx_409_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_443_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_410_, v___x_448_, v___x_449_, v_paramsImpure_437_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_450_);
v___x_452_ = v___x_446_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_paramsPure_436_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_letDeclsPure_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_letDeclsImpure_439_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_funDeclsPure_440_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_funDeclsImpure_441_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(lean_object* v_pu_461_, lean_object* v_lctx_462_, lean_object* v_ps_463_){
_start:
{
uint8_t v_pu_boxed_464_; lean_object* v_res_465_; 
v_pu_boxed_464_ = lean_unbox(v_pu_461_);
v_res_465_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_boxed_464_, v_lctx_462_, v_ps_463_);
lean_dec_ref(v_ps_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t v_pu_466_, lean_object* v_lctx_467_, lean_object* v_decl_468_){
_start:
{
if (v_pu_466_ == 0)
{
lean_object* v_paramsPure_469_; lean_object* v_paramsImpure_470_; lean_object* v_letDeclsPure_471_; lean_object* v_letDeclsImpure_472_; lean_object* v_funDeclsPure_473_; lean_object* v_funDeclsImpure_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
v_paramsPure_469_ = lean_ctor_get(v_lctx_467_, 0);
v_paramsImpure_470_ = lean_ctor_get(v_lctx_467_, 1);
v_letDeclsPure_471_ = lean_ctor_get(v_lctx_467_, 2);
v_letDeclsImpure_472_ = lean_ctor_get(v_lctx_467_, 3);
v_funDeclsPure_473_ = lean_ctor_get(v_lctx_467_, 4);
v_funDeclsImpure_474_ = lean_ctor_get(v_lctx_467_, 5);
v_isSharedCheck_483_ = !lean_is_exclusive(v_lctx_467_);
if (v_isSharedCheck_483_ == 0)
{
v___x_476_ = v_lctx_467_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_funDeclsImpure_474_);
lean_inc(v_funDeclsPure_473_);
lean_inc(v_letDeclsImpure_472_);
lean_inc(v_letDeclsPure_471_);
lean_inc(v_paramsImpure_470_);
lean_inc(v_paramsPure_469_);
lean_dec(v_lctx_467_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_fvarId_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_fvarId_478_ = lean_ctor_get(v_decl_468_, 0);
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsPure_471_, v_fvarId_478_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_paramsPure_469_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_paramsImpure_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_letDeclsImpure_472_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_funDeclsPure_473_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_funDeclsImpure_474_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_paramsPure_484_; lean_object* v_paramsImpure_485_; lean_object* v_letDeclsPure_486_; lean_object* v_letDeclsImpure_487_; lean_object* v_funDeclsPure_488_; lean_object* v_funDeclsImpure_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_498_; 
v_paramsPure_484_ = lean_ctor_get(v_lctx_467_, 0);
v_paramsImpure_485_ = lean_ctor_get(v_lctx_467_, 1);
v_letDeclsPure_486_ = lean_ctor_get(v_lctx_467_, 2);
v_letDeclsImpure_487_ = lean_ctor_get(v_lctx_467_, 3);
v_funDeclsPure_488_ = lean_ctor_get(v_lctx_467_, 4);
v_funDeclsImpure_489_ = lean_ctor_get(v_lctx_467_, 5);
v_isSharedCheck_498_ = !lean_is_exclusive(v_lctx_467_);
if (v_isSharedCheck_498_ == 0)
{
v___x_491_ = v_lctx_467_;
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_funDeclsImpure_489_);
lean_inc(v_funDeclsPure_488_);
lean_inc(v_letDeclsImpure_487_);
lean_inc(v_letDeclsPure_486_);
lean_inc(v_paramsImpure_485_);
lean_inc(v_paramsPure_484_);
lean_dec(v_lctx_467_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_fvarId_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v_fvarId_493_ = lean_ctor_get(v_decl_468_, 0);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsImpure_487_, v_fvarId_493_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 3, v___x_494_);
v___x_496_ = v___x_491_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_paramsPure_484_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_paramsImpure_485_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_letDeclsPure_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_funDeclsPure_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 5, v_funDeclsImpure_489_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(lean_object* v_pu_499_, lean_object* v_lctx_500_, lean_object* v_decl_501_){
_start:
{
uint8_t v_pu_boxed_502_; lean_object* v_res_503_; 
v_pu_boxed_502_ = lean_unbox(v_pu_499_);
v_res_503_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_boxed_502_, v_lctx_500_, v_decl_501_);
lean_dec_ref(v_decl_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t v_pu_504_, lean_object* v_lctx_505_, lean_object* v_decl_506_, uint8_t v_recursive_507_){
_start:
{
lean_object* v___y_509_; 
if (v_pu_504_ == 0)
{
lean_object* v_fvarId_514_; lean_object* v_paramsPure_515_; lean_object* v_paramsImpure_516_; lean_object* v_letDeclsPure_517_; lean_object* v_letDeclsImpure_518_; lean_object* v_funDeclsPure_519_; lean_object* v_funDeclsImpure_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_fvarId_514_ = lean_ctor_get(v_decl_506_, 0);
v_paramsPure_515_ = lean_ctor_get(v_lctx_505_, 0);
v_paramsImpure_516_ = lean_ctor_get(v_lctx_505_, 1);
v_letDeclsPure_517_ = lean_ctor_get(v_lctx_505_, 2);
v_letDeclsImpure_518_ = lean_ctor_get(v_lctx_505_, 3);
v_funDeclsPure_519_ = lean_ctor_get(v_lctx_505_, 4);
v_funDeclsImpure_520_ = lean_ctor_get(v_lctx_505_, 5);
v_isSharedCheck_528_ = !lean_is_exclusive(v_lctx_505_);
if (v_isSharedCheck_528_ == 0)
{
v___x_522_ = v_lctx_505_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_funDeclsImpure_520_);
lean_inc(v_funDeclsPure_519_);
lean_inc(v_letDeclsImpure_518_);
lean_inc(v_letDeclsPure_517_);
lean_inc(v_paramsImpure_516_);
lean_inc(v_paramsPure_515_);
lean_dec(v_lctx_505_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsPure_519_, v_fvarId_514_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_paramsPure_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_paramsImpure_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_letDeclsPure_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_letDeclsImpure_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 5, v_funDeclsImpure_520_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_509_ = v___x_526_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v_fvarId_529_; lean_object* v_paramsPure_530_; lean_object* v_paramsImpure_531_; lean_object* v_letDeclsPure_532_; lean_object* v_letDeclsImpure_533_; lean_object* v_funDeclsPure_534_; lean_object* v_funDeclsImpure_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
v_fvarId_529_ = lean_ctor_get(v_decl_506_, 0);
v_paramsPure_530_ = lean_ctor_get(v_lctx_505_, 0);
v_paramsImpure_531_ = lean_ctor_get(v_lctx_505_, 1);
v_letDeclsPure_532_ = lean_ctor_get(v_lctx_505_, 2);
v_letDeclsImpure_533_ = lean_ctor_get(v_lctx_505_, 3);
v_funDeclsPure_534_ = lean_ctor_get(v_lctx_505_, 4);
v_funDeclsImpure_535_ = lean_ctor_get(v_lctx_505_, 5);
v_isSharedCheck_543_ = !lean_is_exclusive(v_lctx_505_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v_lctx_505_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_funDeclsImpure_535_);
lean_inc(v_funDeclsPure_534_);
lean_inc(v_letDeclsImpure_533_);
lean_inc(v_letDeclsPure_532_);
lean_inc(v_paramsImpure_531_);
lean_inc(v_paramsPure_530_);
lean_dec(v_lctx_505_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsImpure_535_, v_fvarId_529_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 5, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_paramsPure_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_paramsImpure_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_letDeclsPure_532_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_letDeclsImpure_533_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_funDeclsPure_534_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v___y_509_ = v___x_541_;
goto v___jp_508_;
}
}
}
v___jp_508_:
{
if (v_recursive_507_ == 0)
{
return v___y_509_;
}
else
{
lean_object* v_params_510_; lean_object* v_value_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_params_510_ = lean_ctor_get(v_decl_506_, 2);
v_value_511_ = lean_ctor_get(v_decl_506_, 4);
v___x_512_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_504_, v___y_509_, v_params_510_);
v___x_513_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_504_, v_value_511_, v___x_512_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t v_pu_544_, lean_object* v_code_545_, lean_object* v_lctx_546_){
_start:
{
switch(lean_obj_tag(v_code_545_))
{
case 0:
{
lean_object* v_decl_547_; lean_object* v_k_548_; lean_object* v___x_549_; 
v_decl_547_ = lean_ctor_get(v_code_545_, 0);
v_k_548_ = lean_ctor_get(v_code_545_, 1);
v___x_549_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_544_, v_lctx_546_, v_decl_547_);
v_code_545_ = v_k_548_;
v_lctx_546_ = v___x_549_;
goto _start;
}
case 1:
{
lean_object* v_decl_551_; lean_object* v_k_552_; uint8_t v___x_553_; lean_object* v___x_554_; 
v_decl_551_ = lean_ctor_get(v_code_545_, 0);
v_k_552_ = lean_ctor_get(v_code_545_, 1);
v___x_553_ = 1;
v___x_554_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_544_, v_lctx_546_, v_decl_551_, v___x_553_);
v_code_545_ = v_k_552_;
v_lctx_546_ = v___x_554_;
goto _start;
}
case 2:
{
lean_object* v_decl_556_; lean_object* v_k_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
v_decl_556_ = lean_ctor_get(v_code_545_, 0);
v_k_557_ = lean_ctor_get(v_code_545_, 1);
v___x_558_ = 1;
v___x_559_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_544_, v_lctx_546_, v_decl_556_, v___x_558_);
v_code_545_ = v_k_557_;
v_lctx_546_ = v___x_559_;
goto _start;
}
case 4:
{
lean_object* v_cases_561_; lean_object* v_alts_562_; lean_object* v___x_563_; 
v_cases_561_ = lean_ctor_get(v_code_545_, 0);
v_alts_562_ = lean_ctor_get(v_cases_561_, 3);
v___x_563_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_544_, v_alts_562_, v_lctx_546_);
return v___x_563_;
}
case 7:
{
lean_object* v_k_564_; 
v_k_564_ = lean_ctor_get(v_code_545_, 3);
v_code_545_ = v_k_564_;
goto _start;
}
case 8:
{
lean_object* v_k_566_; 
v_k_566_ = lean_ctor_get(v_code_545_, 3);
v_code_545_ = v_k_566_;
goto _start;
}
case 9:
{
lean_object* v_k_568_; 
v_k_568_ = lean_ctor_get(v_code_545_, 5);
v_code_545_ = v_k_568_;
goto _start;
}
case 10:
{
lean_object* v_k_570_; 
v_k_570_ = lean_ctor_get(v_code_545_, 2);
v_code_545_ = v_k_570_;
goto _start;
}
case 11:
{
lean_object* v_k_572_; 
v_k_572_ = lean_ctor_get(v_code_545_, 2);
v_code_545_ = v_k_572_;
goto _start;
}
case 12:
{
lean_object* v_k_574_; 
v_k_574_ = lean_ctor_get(v_code_545_, 3);
v_code_545_ = v_k_574_;
goto _start;
}
case 13:
{
lean_object* v_k_576_; 
v_k_576_ = lean_ctor_get(v_code_545_, 1);
v_code_545_ = v_k_576_;
goto _start;
}
default: 
{
return v_lctx_546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(uint8_t v_pu_578_, lean_object* v_as_579_, size_t v_i_580_, size_t v_stop_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___y_584_; uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_eq(v_i_580_, v_stop_581_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_array_uget_borrowed(v_as_579_, v_i_580_);
switch(lean_obj_tag(v___x_589_))
{
case 0:
{
lean_object* v_params_590_; lean_object* v_code_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_params_590_ = lean_ctor_get(v___x_589_, 1);
v_code_591_ = lean_ctor_get(v___x_589_, 2);
v___x_592_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_578_, v_b_582_, v_params_590_);
v___x_593_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_578_, v_code_591_, v___x_592_);
v___y_584_ = v___x_593_;
goto v___jp_583_;
}
case 1:
{
lean_object* v_code_594_; lean_object* v___x_595_; 
v_code_594_ = lean_ctor_get(v___x_589_, 1);
v___x_595_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_578_, v_code_594_, v_b_582_);
v___y_584_ = v___x_595_;
goto v___jp_583_;
}
default: 
{
lean_object* v_code_596_; lean_object* v___x_597_; 
v_code_596_ = lean_ctor_get(v___x_589_, 0);
v___x_597_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_578_, v_code_596_, v_b_582_);
v___y_584_ = v___x_597_;
goto v___jp_583_;
}
}
}
else
{
return v_b_582_;
}
v___jp_583_:
{
size_t v___x_585_; size_t v___x_586_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_580_, v___x_585_);
v_i_580_ = v___x_586_;
v_b_582_ = v___y_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts(uint8_t v_pu_598_, lean_object* v_alts_599_, lean_object* v_lctx_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_array_get_size(v_alts_599_);
v___x_603_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
return v_lctx_600_;
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_602_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_598_, v_alts_599_, v___x_604_, v___x_605_, v_lctx_600_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(lean_object* v_pu_607_, lean_object* v_alts_608_, lean_object* v_lctx_609_){
_start:
{
uint8_t v_pu_boxed_610_; lean_object* v_res_611_; 
v_pu_boxed_610_ = lean_unbox(v_pu_607_);
v_res_611_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_boxed_610_, v_alts_608_, v_lctx_609_);
lean_dec_ref(v_alts_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(lean_object* v_pu_612_, lean_object* v_as_613_, lean_object* v_i_614_, lean_object* v_stop_615_, lean_object* v_b_616_){
_start:
{
uint8_t v_pu_boxed_617_; size_t v_i_boxed_618_; size_t v_stop_boxed_619_; lean_object* v_res_620_; 
v_pu_boxed_617_ = lean_unbox(v_pu_612_);
v_i_boxed_618_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_stop_boxed_619_ = lean_unbox_usize(v_stop_615_);
lean_dec(v_stop_615_);
v_res_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_boxed_617_, v_as_613_, v_i_boxed_618_, v_stop_boxed_619_, v_b_616_);
lean_dec_ref(v_as_613_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(lean_object* v_pu_621_, lean_object* v_lctx_622_, lean_object* v_decl_623_, lean_object* v_recursive_624_){
_start:
{
uint8_t v_pu_boxed_625_; uint8_t v_recursive_boxed_626_; lean_object* v_res_627_; 
v_pu_boxed_625_ = lean_unbox(v_pu_621_);
v_recursive_boxed_626_ = lean_unbox(v_recursive_624_);
v_res_627_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_boxed_625_, v_lctx_622_, v_decl_623_, v_recursive_boxed_626_);
lean_dec_ref(v_decl_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(lean_object* v_pu_628_, lean_object* v_code_629_, lean_object* v_lctx_630_){
_start:
{
uint8_t v_pu_boxed_631_; lean_object* v_res_632_; 
v_pu_boxed_631_ = lean_unbox(v_pu_628_);
v_res_632_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_boxed_631_, v_code_629_, v_lctx_630_);
lean_dec_ref(v_code_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params(lean_object* v_lctx_633_, uint8_t v_pu_634_){
_start:
{
if (v_pu_634_ == 0)
{
lean_object* v_paramsPure_635_; 
v_paramsPure_635_ = lean_ctor_get(v_lctx_633_, 0);
lean_inc_ref(v_paramsPure_635_);
return v_paramsPure_635_;
}
else
{
lean_object* v_paramsImpure_636_; 
v_paramsImpure_636_ = lean_ctor_get(v_lctx_633_, 1);
lean_inc_ref(v_paramsImpure_636_);
return v_paramsImpure_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params___boxed(lean_object* v_lctx_637_, lean_object* v_pu_638_){
_start:
{
uint8_t v_pu_boxed_639_; lean_object* v_res_640_; 
v_pu_boxed_639_ = lean_unbox(v_pu_638_);
v_res_640_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_637_, v_pu_boxed_639_);
lean_dec_ref(v_lctx_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls(lean_object* v_lctx_641_, uint8_t v_pu_642_){
_start:
{
if (v_pu_642_ == 0)
{
lean_object* v_letDeclsPure_643_; 
v_letDeclsPure_643_ = lean_ctor_get(v_lctx_641_, 2);
lean_inc_ref(v_letDeclsPure_643_);
return v_letDeclsPure_643_;
}
else
{
lean_object* v_letDeclsImpure_644_; 
v_letDeclsImpure_644_ = lean_ctor_get(v_lctx_641_, 3);
lean_inc_ref(v_letDeclsImpure_644_);
return v_letDeclsImpure_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(lean_object* v_lctx_645_, lean_object* v_pu_646_){
_start:
{
uint8_t v_pu_boxed_647_; lean_object* v_res_648_; 
v_pu_boxed_647_ = lean_unbox(v_pu_646_);
v_res_648_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_645_, v_pu_boxed_647_);
lean_dec_ref(v_lctx_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls(lean_object* v_lctx_649_, uint8_t v_pu_650_){
_start:
{
if (v_pu_650_ == 0)
{
lean_object* v_funDeclsPure_651_; 
v_funDeclsPure_651_ = lean_ctor_get(v_lctx_649_, 4);
lean_inc_ref(v_funDeclsPure_651_);
return v_funDeclsPure_651_;
}
else
{
lean_object* v_funDeclsImpure_652_; 
v_funDeclsImpure_652_ = lean_ctor_get(v_lctx_649_, 5);
lean_inc_ref(v_funDeclsImpure_652_);
return v_funDeclsImpure_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(lean_object* v_lctx_653_, lean_object* v_pu_654_){
_start:
{
uint8_t v_pu_boxed_655_; lean_object* v_res_656_; 
v_pu_boxed_655_ = lean_unbox(v_pu_654_);
v_res_656_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_653_, v_pu_boxed_655_);
lean_dec_ref(v_lctx_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
if (lean_obj_tag(v_a_657_) == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v_a_658_);
return v___x_659_;
}
else
{
lean_object* v_value_660_; lean_object* v_tail_661_; lean_object* v_fvarId_662_; lean_object* v_binderName_663_; lean_object* v_type_664_; lean_object* v___x_665_; uint8_t v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_value_660_ = lean_ctor_get(v_a_657_, 1);
v_tail_661_ = lean_ctor_get(v_a_657_, 2);
v_fvarId_662_ = lean_ctor_get(v_value_660_, 0);
v_binderName_663_ = lean_ctor_get(v_value_660_, 1);
v_type_664_ = lean_ctor_get(v_value_660_, 3);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = 0;
v___x_667_ = 0;
lean_inc_ref(v_type_664_);
lean_inc(v_binderName_663_);
lean_inc(v_fvarId_662_);
v___x_668_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_668_, 0, v___x_665_);
lean_ctor_set(v___x_668_, 1, v_fvarId_662_);
lean_ctor_set(v___x_668_, 2, v_binderName_663_);
lean_ctor_set(v___x_668_, 3, v_type_664_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*4, v___x_666_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*4 + 1, v___x_667_);
v___x_669_ = l_Lean_LocalContext_addDecl(v_a_658_, v___x_668_);
v_a_657_ = v_tail_661_;
v_a_658_ = v___x_669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_671_, v_a_672_);
lean_dec(v_a_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(lean_object* v_as_674_, size_t v_sz_675_, size_t v_i_676_, lean_object* v_b_677_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
if (v___x_678_ == 0)
{
return v_b_677_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_array_uget_borrowed(v_as_674_, v_i_676_);
v___x_680_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_679_, v_b_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
return v_a_681_;
}
else
{
lean_object* v_a_682_; size_t v___x_683_; size_t v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_680_, 1);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_676_, v___x_683_);
v_i_676_ = v___x_684_;
v_b_677_ = v_a_682_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5___boxed(lean_object* v_as_686_, lean_object* v_sz_687_, lean_object* v_i_688_, lean_object* v_b_689_){
_start:
{
size_t v_sz_boxed_690_; size_t v_i_boxed_691_; lean_object* v_res_692_; 
v_sz_boxed_690_ = lean_unbox_usize(v_sz_687_);
lean_dec(v_sz_687_);
v_i_boxed_691_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_as_686_, v_sz_boxed_690_, v_i_boxed_691_, v_b_689_);
lean_dec_ref(v_as_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(uint8_t v_pu_693_, lean_object* v_a_694_, lean_object* v_a_695_){
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
lean_object* v_value_697_; lean_object* v_tail_698_; lean_object* v_fvarId_699_; lean_object* v_binderName_700_; lean_object* v_type_701_; lean_object* v_value_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_value_697_ = lean_ctor_get(v_a_694_, 1);
lean_inc(v_value_697_);
v_tail_698_ = lean_ctor_get(v_a_694_, 2);
lean_inc(v_tail_698_);
lean_dec_ref_known(v_a_694_, 3);
v_fvarId_699_ = lean_ctor_get(v_value_697_, 0);
lean_inc(v_fvarId_699_);
v_binderName_700_ = lean_ctor_get(v_value_697_, 1);
lean_inc(v_binderName_700_);
v_type_701_ = lean_ctor_get(v_value_697_, 2);
lean_inc_ref(v_type_701_);
v_value_702_ = lean_ctor_get(v_value_697_, 3);
lean_inc(v_value_702_);
lean_dec(v_value_697_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_693_, v_value_702_);
v___x_705_ = 1;
v___x_706_ = 0;
v___x_707_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_707_, 0, v___x_703_);
lean_ctor_set(v___x_707_, 1, v_fvarId_699_);
lean_ctor_set(v___x_707_, 2, v_binderName_700_);
lean_ctor_set(v___x_707_, 3, v_type_701_);
lean_ctor_set(v___x_707_, 4, v___x_704_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*5, v___x_705_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*5 + 1, v___x_706_);
v___x_708_ = l_Lean_LocalContext_addDecl(v_a_695_, v___x_707_);
v_a_694_ = v_tail_698_;
v_a_695_ = v___x_708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object* v_pu_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
uint8_t v_pu_boxed_713_; lean_object* v_res_714_; 
v_pu_boxed_713_ = lean_unbox(v_pu_710_);
v_res_714_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_boxed_713_, v_a_711_, v_a_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(uint8_t v_pu_715_, lean_object* v_as_716_, size_t v_sz_717_, size_t v_i_718_, lean_object* v_b_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_718_, v_sz_717_);
if (v___x_720_ == 0)
{
return v_b_719_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_721_ = lean_array_uget_borrowed(v_as_716_, v_i_718_);
lean_inc(v_a_721_);
v___x_722_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_715_, v_a_721_, v_b_719_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
return v_a_723_;
}
else
{
lean_object* v_a_724_; size_t v___x_725_; size_t v___x_726_; 
v_a_724_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_722_, 1);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_718_, v___x_725_);
v_i_718_ = v___x_726_;
v_b_719_ = v_a_724_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4___boxed(lean_object* v_pu_728_, lean_object* v_as_729_, lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_b_732_){
_start:
{
uint8_t v_pu_boxed_733_; size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_pu_boxed_733_ = lean_unbox(v_pu_728_);
v_sz_boxed_734_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_735_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_boxed_733_, v_as_729_, v_sz_boxed_734_, v_i_boxed_735_, v_b_732_);
lean_dec_ref(v_as_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
if (lean_obj_tag(v_a_737_) == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_a_738_);
return v___x_739_;
}
else
{
lean_object* v_value_740_; lean_object* v_tail_741_; lean_object* v_fvarId_742_; lean_object* v_binderName_743_; lean_object* v_type_744_; lean_object* v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_value_740_ = lean_ctor_get(v_a_737_, 1);
v_tail_741_ = lean_ctor_get(v_a_737_, 2);
v_fvarId_742_ = lean_ctor_get(v_value_740_, 0);
v_binderName_743_ = lean_ctor_get(v_value_740_, 1);
v_type_744_ = lean_ctor_get(v_value_740_, 2);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = 0;
v___x_747_ = 0;
lean_inc_ref(v_type_744_);
lean_inc(v_binderName_743_);
lean_inc(v_fvarId_742_);
v___x_748_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_748_, 0, v___x_745_);
lean_ctor_set(v___x_748_, 1, v_fvarId_742_);
lean_ctor_set(v___x_748_, 2, v_binderName_743_);
lean_ctor_set(v___x_748_, 3, v_type_744_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*4, v___x_746_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*4 + 1, v___x_747_);
v___x_749_ = l_Lean_LocalContext_addDecl(v_a_738_, v___x_748_);
v_a_737_ = v_tail_741_;
v_a_738_ = v___x_749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_751_, v_a_752_);
lean_dec(v_a_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(lean_object* v_as_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_b_757_){
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
v___x_760_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_759_, v_b_757_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3___boxed(lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_b_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_771_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_as_766_, v_sz_boxed_770_, v_i_boxed_771_, v_b_769_);
lean_dec_ref(v_as_766_);
return v_res_772_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0(void){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(32u);
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3(void){
_start:
{
size_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_779_ = ((size_t)5ULL);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_unsigned_to_nat(32u);
v___x_782_ = lean_mk_empty_array_with_capacity(v___x_781_);
v___x_783_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2);
v___x_784_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
lean_ctor_set(v___x_784_, 2, v___x_780_);
lean_ctor_set(v___x_784_, 3, v___x_780_);
lean_ctor_set_usize(v___x_784_, 4, v___x_779_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v_result_788_; 
v___x_785_ = lean_box(1);
v___x_786_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3);
v___x_787_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1);
v_result_788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_788_, 0, v___x_787_);
lean_ctor_set(v_result_788_, 1, v___x_786_);
lean_ctor_set(v_result_788_, 2, v___x_785_);
return v_result_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object* v_lctx_789_, uint8_t v_pu_790_){
_start:
{
lean_object* v___y_792_; size_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_799_; size_t v___y_800_; lean_object* v___y_801_; lean_object* v_result_807_; lean_object* v___y_809_; 
v_result_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4);
if (v_pu_790_ == 0)
{
lean_object* v_paramsPure_816_; 
v_paramsPure_816_ = lean_ctor_get(v_lctx_789_, 0);
v___y_809_ = v_paramsPure_816_;
goto v___jp_808_;
}
else
{
lean_object* v_paramsImpure_817_; 
v_paramsImpure_817_ = lean_ctor_get(v_lctx_789_, 1);
v___y_809_ = v_paramsImpure_817_;
goto v___jp_808_;
}
v___jp_791_:
{
lean_object* v_buckets_795_; size_t v_sz_796_; lean_object* v___x_797_; 
v_buckets_795_ = lean_ctor_get(v___y_794_, 1);
v_sz_796_ = lean_array_size(v_buckets_795_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_buckets_795_, v_sz_796_, v___y_793_, v___y_792_);
return v___x_797_;
}
v___jp_798_:
{
lean_object* v_buckets_802_; size_t v_sz_803_; lean_object* v___x_804_; 
v_buckets_802_ = lean_ctor_get(v___y_801_, 1);
v_sz_803_ = lean_array_size(v_buckets_802_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_790_, v_buckets_802_, v_sz_803_, v___y_800_, v___y_799_);
if (v_pu_790_ == 0)
{
lean_object* v_funDeclsPure_805_; 
v_funDeclsPure_805_ = lean_ctor_get(v_lctx_789_, 4);
v___y_792_ = v___x_804_;
v___y_793_ = v___y_800_;
v___y_794_ = v_funDeclsPure_805_;
goto v___jp_791_;
}
else
{
lean_object* v_funDeclsImpure_806_; 
v_funDeclsImpure_806_ = lean_ctor_get(v_lctx_789_, 5);
v___y_792_ = v___x_804_;
v___y_793_ = v___y_800_;
v___y_794_ = v_funDeclsImpure_806_;
goto v___jp_791_;
}
}
v___jp_808_:
{
lean_object* v_buckets_810_; size_t v_sz_811_; size_t v___x_812_; lean_object* v___x_813_; 
v_buckets_810_ = lean_ctor_get(v___y_809_, 1);
v_sz_811_ = lean_array_size(v_buckets_810_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_buckets_810_, v_sz_811_, v___x_812_, v_result_807_);
if (v_pu_790_ == 0)
{
lean_object* v_letDeclsPure_814_; 
v_letDeclsPure_814_ = lean_ctor_get(v_lctx_789_, 2);
v___y_799_ = v___x_813_;
v___y_800_ = v___x_812_;
v___y_801_ = v_letDeclsPure_814_;
goto v___jp_798_;
}
else
{
lean_object* v_letDeclsImpure_815_; 
v_letDeclsImpure_815_ = lean_ctor_get(v_lctx_789_, 3);
v___y_799_ = v___x_813_;
v___y_800_ = v___x_812_;
v___y_801_ = v_letDeclsImpure_815_;
goto v___jp_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(lean_object* v_lctx_818_, lean_object* v_pu_819_){
_start:
{
uint8_t v_pu_boxed_820_; lean_object* v_res_821_; 
v_pu_boxed_820_ = lean_unbox(v_pu_819_);
v_res_821_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_818_, v_pu_boxed_820_);
lean_dec_ref(v_lctx_818_);
return v_res_821_;
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
