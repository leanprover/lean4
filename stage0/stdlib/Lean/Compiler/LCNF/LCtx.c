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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(lean_object* v_a_11_, lean_object* v_x_12_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[0].m_obj;
lean_object* v_x_12_ = stack[1].m_obj;
uint8_t v_res_18_;
v_res_18_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_11_, v_x_12_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg___boxed(lean_object* v_a_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_19_, v_x_20_);
lean_dec(v_x_20_);
lean_dec(v_a_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
return v_x_23_;
}
else
{
lean_object* v_key_25_; lean_object* v_value_26_; lean_object* v_tail_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_50_; 
v_key_25_ = lean_ctor_get(v_x_24_, 0);
v_value_26_ = lean_ctor_get(v_x_24_, 1);
v_tail_27_ = lean_ctor_get(v_x_24_, 2);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_24_);
if (v_isSharedCheck_50_ == 0)
{
v___x_29_ = v_x_24_;
v_isShared_30_ = v_isSharedCheck_50_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_tail_27_);
lean_inc(v_value_26_);
lean_inc(v_key_25_);
lean_dec(v_x_24_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_50_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v_fold_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_31_ = lean_array_get_size(v_x_23_);
v___x_32_ = l_Lean_instHashableFVarId_hash(v_key_25_);
v___x_33_ = 32ULL;
v___x_34_ = lean_uint64_shift_right(v___x_32_, v___x_33_);
v_fold_35_ = lean_uint64_xor(v___x_32_, v___x_34_);
v___x_36_ = 16ULL;
v___x_37_ = lean_uint64_shift_right(v_fold_35_, v___x_36_);
v___x_38_ = lean_uint64_xor(v_fold_35_, v___x_37_);
v___x_39_ = lean_uint64_to_usize(v___x_38_);
v___x_40_ = lean_usize_of_nat(v___x_31_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_sub(v___x_40_, v___x_41_);
v___x_43_ = lean_usize_land(v___x_39_, v___x_42_);
v___x_44_ = lean_array_uget_borrowed(v_x_23_, v___x_43_);
lean_inc(v___x_44_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v___x_44_);
v___x_46_ = v___x_29_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_key_25_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_value_26_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v___x_44_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
v___x_47_ = lean_array_uset(v_x_23_, v___x_43_, v___x_46_);
v_x_23_ = v___x_47_;
v_x_24_ = v_tail_27_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(lean_object* v_i_51_, lean_object* v_source_52_, lean_object* v_target_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v_source_52_);
v___x_55_ = lean_nat_dec_lt(v_i_51_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v_source_52_);
lean_dec(v_i_51_);
return v_target_53_;
}
else
{
lean_object* v_es_56_; lean_object* v___x_57_; lean_object* v_source_58_; lean_object* v_target_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_es_56_ = lean_array_fget(v_source_52_, v_i_51_);
v___x_57_ = lean_box(0);
v_source_58_ = lean_array_fset(v_source_52_, v_i_51_, v___x_57_);
v_target_59_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_target_53_, v_es_56_);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_add(v_i_51_, v___x_60_);
lean_dec(v_i_51_);
v_i_51_ = v___x_61_;
v_source_52_ = v_source_58_;
v_target_53_ = v_target_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(lean_object* v_data_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_nbuckets_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_64_ = lean_array_get_size(v_data_63_);
v___x_65_ = lean_unsigned_to_nat(2u);
v_nbuckets_66_ = lean_nat_mul(v___x_64_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_box(0);
v___x_69_ = lean_mk_array(v_nbuckets_66_, v___x_68_);
v___x_70_ = lean_array_propagate_mark(v_data_63_, v___x_69_);
v___x_71_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v___x_67_, v_data_63_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(lean_object* v_a_72_, lean_object* v_b_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_dec(v_b_73_);
lean_dec(v_a_72_);
return v_x_74_;
}
else
{
lean_object* v_key_75_; lean_object* v_value_76_; lean_object* v_tail_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_89_; 
v_key_75_ = lean_ctor_get(v_x_74_, 0);
v_value_76_ = lean_ctor_get(v_x_74_, 1);
v_tail_77_ = lean_ctor_get(v_x_74_, 2);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_89_ == 0)
{
v___x_79_ = v_x_74_;
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_tail_77_);
lean_inc(v_value_76_);
lean_inc(v_key_75_);
lean_dec(v_x_74_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_instBEqFVarId_beq(v_key_75_, v_a_72_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_72_, v_b_73_, v_tail_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 2, v___x_82_);
v___x_84_ = v___x_79_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_key_75_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_value_76_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_value_76_);
lean_dec(v_key_75_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v_b_73_);
lean_ctor_set(v___x_79_, 0, v_a_72_);
v___x_87_ = v___x_79_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_72_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_b_73_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_tail_77_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object* v_m_90_, lean_object* v_a_91_, lean_object* v_b_92_){
_start:
{
lean_object* v_size_93_; lean_object* v_buckets_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_137_; 
v_size_93_ = lean_ctor_get(v_m_90_, 0);
v_buckets_94_ = lean_ctor_get(v_m_90_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_m_90_);
if (v_isSharedCheck_137_ == 0)
{
v___x_96_ = v_m_90_;
v_isShared_97_ = v_isSharedCheck_137_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_buckets_94_);
lean_inc(v_size_93_);
lean_dec(v_m_90_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_137_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v_fold_102_; uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; lean_object* v_bkt_111_; uint8_t v___x_112_; 
v___x_98_ = lean_array_get_size(v_buckets_94_);
v___x_99_ = l_Lean_instHashableFVarId_hash(v_a_91_);
v___x_100_ = 32ULL;
v___x_101_ = lean_uint64_shift_right(v___x_99_, v___x_100_);
v_fold_102_ = lean_uint64_xor(v___x_99_, v___x_101_);
v___x_103_ = 16ULL;
v___x_104_ = lean_uint64_shift_right(v_fold_102_, v___x_103_);
v___x_105_ = lean_uint64_xor(v_fold_102_, v___x_104_);
v___x_106_ = lean_uint64_to_usize(v___x_105_);
v___x_107_ = lean_usize_of_nat(v___x_98_);
v___x_108_ = ((size_t)1ULL);
v___x_109_ = lean_usize_sub(v___x_107_, v___x_108_);
v___x_110_ = lean_usize_land(v___x_106_, v___x_109_);
v_bkt_111_ = lean_array_uget_borrowed(v_buckets_94_, v___x_110_);
v___x_112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_91_, v_bkt_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v_size_x27_114_; lean_object* v___x_115_; lean_object* v_buckets_x27_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v_size_x27_114_ = lean_nat_add(v_size_93_, v___x_113_);
lean_dec(v_size_93_);
lean_inc(v_bkt_111_);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v_a_91_);
lean_ctor_set(v___x_115_, 1, v_b_92_);
lean_ctor_set(v___x_115_, 2, v_bkt_111_);
v_buckets_x27_116_ = lean_array_uset(v_buckets_94_, v___x_110_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(4u);
v___x_118_ = lean_nat_mul(v_size_x27_114_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(3u);
v___x_120_ = lean_nat_div(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_array_get_size(v_buckets_x27_116_);
v___x_122_ = lean_nat_dec_le(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
if (v___x_122_ == 0)
{
lean_object* v_val_123_; lean_object* v___x_125_; 
v_val_123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_buckets_x27_116_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_val_123_);
lean_ctor_set(v___x_96_, 0, v_size_x27_114_);
v___x_125_ = v___x_96_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_size_x27_114_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_val_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v___x_128_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_buckets_x27_116_);
lean_ctor_set(v___x_96_, 0, v_size_x27_114_);
v___x_128_ = v___x_96_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_size_x27_114_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_buckets_x27_116_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v___x_130_; lean_object* v_buckets_x27_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
lean_inc(v_bkt_111_);
v___x_130_ = lean_box(0);
v_buckets_x27_131_ = lean_array_uset(v_buckets_94_, v___x_110_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_91_, v_b_92_, v_bkt_111_);
v___x_133_ = lean_array_uset(v_buckets_x27_131_, v___x_110_, v___x_132_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_133_);
v___x_135_ = v___x_96_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_93_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t v_pu_138_, lean_object* v_lctx_139_, lean_object* v_param_140_){
_start:
{
if (v_pu_138_ == 0)
{
lean_object* v_paramsPure_141_; lean_object* v_paramsImpure_142_; lean_object* v_letDeclsPure_143_; lean_object* v_letDeclsImpure_144_; lean_object* v_funDeclsPure_145_; lean_object* v_funDeclsImpure_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_155_; 
v_paramsPure_141_ = lean_ctor_get(v_lctx_139_, 0);
v_paramsImpure_142_ = lean_ctor_get(v_lctx_139_, 1);
v_letDeclsPure_143_ = lean_ctor_get(v_lctx_139_, 2);
v_letDeclsImpure_144_ = lean_ctor_get(v_lctx_139_, 3);
v_funDeclsPure_145_ = lean_ctor_get(v_lctx_139_, 4);
v_funDeclsImpure_146_ = lean_ctor_get(v_lctx_139_, 5);
v_isSharedCheck_155_ = !lean_is_exclusive(v_lctx_139_);
if (v_isSharedCheck_155_ == 0)
{
v___x_148_ = v_lctx_139_;
v_isShared_149_ = v_isSharedCheck_155_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_funDeclsImpure_146_);
lean_inc(v_funDeclsPure_145_);
lean_inc(v_letDeclsImpure_144_);
lean_inc(v_letDeclsPure_143_);
lean_inc(v_paramsImpure_142_);
lean_inc(v_paramsPure_141_);
lean_dec(v_lctx_139_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_155_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_fvarId_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v_fvarId_150_ = lean_ctor_get(v_param_140_, 0);
lean_inc(v_fvarId_150_);
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsPure_141_, v_fvarId_150_, v_param_140_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_151_);
v___x_153_ = v___x_148_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_paramsImpure_142_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_letDeclsPure_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_letDeclsImpure_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_funDeclsPure_145_);
lean_ctor_set(v_reuseFailAlloc_154_, 5, v_funDeclsImpure_146_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_paramsPure_156_; lean_object* v_paramsImpure_157_; lean_object* v_letDeclsPure_158_; lean_object* v_letDeclsImpure_159_; lean_object* v_funDeclsPure_160_; lean_object* v_funDeclsImpure_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_170_; 
v_paramsPure_156_ = lean_ctor_get(v_lctx_139_, 0);
v_paramsImpure_157_ = lean_ctor_get(v_lctx_139_, 1);
v_letDeclsPure_158_ = lean_ctor_get(v_lctx_139_, 2);
v_letDeclsImpure_159_ = lean_ctor_get(v_lctx_139_, 3);
v_funDeclsPure_160_ = lean_ctor_get(v_lctx_139_, 4);
v_funDeclsImpure_161_ = lean_ctor_get(v_lctx_139_, 5);
v_isSharedCheck_170_ = !lean_is_exclusive(v_lctx_139_);
if (v_isSharedCheck_170_ == 0)
{
v___x_163_ = v_lctx_139_;
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_funDeclsImpure_161_);
lean_inc(v_funDeclsPure_160_);
lean_inc(v_letDeclsImpure_159_);
lean_inc(v_letDeclsPure_158_);
lean_inc(v_paramsImpure_157_);
lean_inc(v_paramsPure_156_);
lean_dec(v_lctx_139_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_fvarId_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v_fvarId_165_ = lean_ctor_get(v_param_140_, 0);
lean_inc(v_fvarId_165_);
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsImpure_157_, v_fvarId_165_, v_param_140_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_166_);
v___x_168_ = v___x_163_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_paramsPure_156_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_letDeclsPure_158_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_letDeclsImpure_159_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_funDeclsPure_160_);
lean_ctor_set(v_reuseFailAlloc_169_, 5, v_funDeclsImpure_161_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_addParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_138_ = stack[0].m_num;
lean_object* v_lctx_139_ = stack[1].m_obj;
lean_object* v_param_140_ = stack[2].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_138_, v_lctx_139_, v_param_140_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam___boxed(lean_object* v_pu_172_, lean_object* v_lctx_173_, lean_object* v_param_174_){
_start:
{
uint8_t v_pu_boxed_175_; lean_object* v_res_176_; 
v_pu_boxed_175_ = lean_unbox(v_pu_172_);
v_res_176_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_boxed_175_, v_lctx_173_, v_param_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object* v_00_u03b2_177_, lean_object* v_m_178_, lean_object* v_a_179_, lean_object* v_b_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_178_, v_a_179_, v_b_180_);
return v___x_181_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_object* v_00_u03b2_182_, lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_183_, v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_183_ = stack[1].m_obj;
lean_object* v_x_184_ = stack[2].m_obj;
uint8_t v_res_186_;
v_res_186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_box(0), v_a_183_, v_x_184_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(v_00_u03b2_187_, v_a_188_, v_x_189_);
lean_dec(v_x_189_);
lean_dec(v_a_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1(lean_object* v_00_u03b2_192_, lean_object* v_data_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_data_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2(lean_object* v_00_u03b2_195_, lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_x_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_196_, v_b_197_, v_x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_200_, lean_object* v_i_201_, lean_object* v_source_202_, lean_object* v_target_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v_i_201_, v_source_202_, v_target_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_x_206_, v_x_207_);
return v___x_208_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t v_pu_209_, lean_object* v_lctx_210_, lean_object* v_letDecl_211_){
_start:
{
if (v_pu_209_ == 0)
{
lean_object* v_paramsPure_212_; lean_object* v_paramsImpure_213_; lean_object* v_letDeclsPure_214_; lean_object* v_letDeclsImpure_215_; lean_object* v_funDeclsPure_216_; lean_object* v_funDeclsImpure_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_226_; 
v_paramsPure_212_ = lean_ctor_get(v_lctx_210_, 0);
v_paramsImpure_213_ = lean_ctor_get(v_lctx_210_, 1);
v_letDeclsPure_214_ = lean_ctor_get(v_lctx_210_, 2);
v_letDeclsImpure_215_ = lean_ctor_get(v_lctx_210_, 3);
v_funDeclsPure_216_ = lean_ctor_get(v_lctx_210_, 4);
v_funDeclsImpure_217_ = lean_ctor_get(v_lctx_210_, 5);
v_isSharedCheck_226_ = !lean_is_exclusive(v_lctx_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_219_ = v_lctx_210_;
v_isShared_220_ = v_isSharedCheck_226_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_funDeclsImpure_217_);
lean_inc(v_funDeclsPure_216_);
lean_inc(v_letDeclsImpure_215_);
lean_inc(v_letDeclsPure_214_);
lean_inc(v_paramsImpure_213_);
lean_inc(v_paramsPure_212_);
lean_dec(v_lctx_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_226_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_fvarId_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v_fvarId_221_ = lean_ctor_get(v_letDecl_211_, 0);
lean_inc(v_fvarId_221_);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsPure_214_, v_fvarId_221_, v_letDecl_211_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 2, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_paramsPure_212_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_paramsImpure_213_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_letDeclsImpure_215_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_funDeclsPure_216_);
lean_ctor_set(v_reuseFailAlloc_225_, 5, v_funDeclsImpure_217_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v_paramsPure_227_; lean_object* v_paramsImpure_228_; lean_object* v_letDeclsPure_229_; lean_object* v_letDeclsImpure_230_; lean_object* v_funDeclsPure_231_; lean_object* v_funDeclsImpure_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_241_; 
v_paramsPure_227_ = lean_ctor_get(v_lctx_210_, 0);
v_paramsImpure_228_ = lean_ctor_get(v_lctx_210_, 1);
v_letDeclsPure_229_ = lean_ctor_get(v_lctx_210_, 2);
v_letDeclsImpure_230_ = lean_ctor_get(v_lctx_210_, 3);
v_funDeclsPure_231_ = lean_ctor_get(v_lctx_210_, 4);
v_funDeclsImpure_232_ = lean_ctor_get(v_lctx_210_, 5);
v_isSharedCheck_241_ = !lean_is_exclusive(v_lctx_210_);
if (v_isSharedCheck_241_ == 0)
{
v___x_234_ = v_lctx_210_;
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_funDeclsImpure_232_);
lean_inc(v_funDeclsPure_231_);
lean_inc(v_letDeclsImpure_230_);
lean_inc(v_letDeclsPure_229_);
lean_inc(v_paramsImpure_228_);
lean_inc(v_paramsPure_227_);
lean_dec(v_lctx_210_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_fvarId_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v_fvarId_236_ = lean_ctor_get(v_letDecl_211_, 0);
lean_inc(v_fvarId_236_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsImpure_230_, v_fvarId_236_, v_letDecl_211_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 3, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_paramsPure_227_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_paramsImpure_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_letDeclsPure_229_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_funDeclsPure_231_);
lean_ctor_set(v_reuseFailAlloc_240_, 5, v_funDeclsImpure_232_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_addLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_209_ = stack[0].m_num;
lean_object* v_lctx_210_ = stack[1].m_obj;
lean_object* v_letDecl_211_ = stack[2].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_209_, v_lctx_210_, v_letDecl_211_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(lean_object* v_pu_243_, lean_object* v_lctx_244_, lean_object* v_letDecl_245_){
_start:
{
uint8_t v_pu_boxed_246_; lean_object* v_res_247_; 
v_pu_boxed_246_ = lean_unbox(v_pu_243_);
v_res_247_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_boxed_246_, v_lctx_244_, v_letDecl_245_);
return v_res_247_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t v_pu_248_, lean_object* v_lctx_249_, lean_object* v_funDecl_250_){
_start:
{
if (v_pu_248_ == 0)
{
lean_object* v_fvarId_251_; lean_object* v_paramsPure_252_; lean_object* v_paramsImpure_253_; lean_object* v_letDeclsPure_254_; lean_object* v_letDeclsImpure_255_; lean_object* v_funDeclsPure_256_; lean_object* v_funDeclsImpure_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_fvarId_251_ = lean_ctor_get(v_funDecl_250_, 0);
lean_inc(v_fvarId_251_);
v_paramsPure_252_ = lean_ctor_get(v_lctx_249_, 0);
v_paramsImpure_253_ = lean_ctor_get(v_lctx_249_, 1);
v_letDeclsPure_254_ = lean_ctor_get(v_lctx_249_, 2);
v_letDeclsImpure_255_ = lean_ctor_get(v_lctx_249_, 3);
v_funDeclsPure_256_ = lean_ctor_get(v_lctx_249_, 4);
v_funDeclsImpure_257_ = lean_ctor_get(v_lctx_249_, 5);
v_isSharedCheck_265_ = !lean_is_exclusive(v_lctx_249_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v_lctx_249_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_funDeclsImpure_257_);
lean_inc(v_funDeclsPure_256_);
lean_inc(v_letDeclsImpure_255_);
lean_inc(v_letDeclsPure_254_);
lean_inc(v_paramsImpure_253_);
lean_inc(v_paramsPure_252_);
lean_dec(v_lctx_249_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsPure_256_, v_fvarId_251_, v_funDecl_250_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 4, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_paramsPure_252_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_paramsImpure_253_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_letDeclsPure_254_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_letDeclsImpure_255_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 5, v_funDeclsImpure_257_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_fvarId_266_; lean_object* v_paramsPure_267_; lean_object* v_paramsImpure_268_; lean_object* v_letDeclsPure_269_; lean_object* v_letDeclsImpure_270_; lean_object* v_funDeclsPure_271_; lean_object* v_funDeclsImpure_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_280_; 
v_fvarId_266_ = lean_ctor_get(v_funDecl_250_, 0);
lean_inc(v_fvarId_266_);
v_paramsPure_267_ = lean_ctor_get(v_lctx_249_, 0);
v_paramsImpure_268_ = lean_ctor_get(v_lctx_249_, 1);
v_letDeclsPure_269_ = lean_ctor_get(v_lctx_249_, 2);
v_letDeclsImpure_270_ = lean_ctor_get(v_lctx_249_, 3);
v_funDeclsPure_271_ = lean_ctor_get(v_lctx_249_, 4);
v_funDeclsImpure_272_ = lean_ctor_get(v_lctx_249_, 5);
v_isSharedCheck_280_ = !lean_is_exclusive(v_lctx_249_);
if (v_isSharedCheck_280_ == 0)
{
v___x_274_ = v_lctx_249_;
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_funDeclsImpure_272_);
lean_inc(v_funDeclsPure_271_);
lean_inc(v_letDeclsImpure_270_);
lean_inc(v_letDeclsPure_269_);
lean_inc(v_paramsImpure_268_);
lean_inc(v_paramsPure_267_);
lean_dec(v_lctx_249_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsImpure_272_, v_fvarId_266_, v_funDecl_250_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 5, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_paramsPure_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_paramsImpure_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_letDeclsPure_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_letDeclsImpure_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_funDeclsPure_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_addFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_248_ = stack[0].m_num;
lean_object* v_lctx_249_ = stack[1].m_obj;
lean_object* v_funDecl_250_ = stack[2].m_obj;
lean_object* v_res_281_;
v_res_281_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_248_, v_lctx_249_, v_funDecl_250_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(lean_object* v_pu_282_, lean_object* v_lctx_283_, lean_object* v_funDecl_284_){
_start:
{
uint8_t v_pu_boxed_285_; lean_object* v_res_286_; 
v_pu_boxed_285_ = lean_unbox(v_pu_282_);
v_res_286_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_boxed_285_, v_lctx_283_, v_funDecl_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
return v_x_288_;
}
else
{
lean_object* v_key_289_; lean_object* v_value_290_; lean_object* v_tail_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_300_; 
v_key_289_ = lean_ctor_get(v_x_288_, 0);
v_value_290_ = lean_ctor_get(v_x_288_, 1);
v_tail_291_ = lean_ctor_get(v_x_288_, 2);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_300_ == 0)
{
v___x_293_ = v_x_288_;
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_tail_291_);
lean_inc(v_value_290_);
lean_inc(v_key_289_);
lean_dec(v_x_288_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; 
v___x_295_ = l_Lean_instBEqFVarId_beq(v_key_289_, v_a_287_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_287_, v_tail_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 2, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_key_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_value_290_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_del_object(v___x_293_);
lean_dec(v_value_290_);
lean_dec(v_key_289_);
return v_tail_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(lean_object* v_a_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_301_, v_x_302_);
lean_dec(v_a_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object* v_m_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_size_306_; lean_object* v_buckets_307_; lean_object* v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v_fold_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; lean_object* v_bkt_321_; uint8_t v___x_322_; 
v_size_306_ = lean_ctor_get(v_m_304_, 0);
v_buckets_307_ = lean_ctor_get(v_m_304_, 1);
v___x_308_ = lean_array_get_size(v_buckets_307_);
v___x_309_ = l_Lean_instHashableFVarId_hash(v_a_305_);
v___x_310_ = 32ULL;
v___x_311_ = lean_uint64_shift_right(v___x_309_, v___x_310_);
v_fold_312_ = lean_uint64_xor(v___x_309_, v___x_311_);
v___x_313_ = 16ULL;
v___x_314_ = lean_uint64_shift_right(v_fold_312_, v___x_313_);
v___x_315_ = lean_uint64_xor(v_fold_312_, v___x_314_);
v___x_316_ = lean_uint64_to_usize(v___x_315_);
v___x_317_ = lean_usize_of_nat(v___x_308_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_sub(v___x_317_, v___x_318_);
v___x_320_ = lean_usize_land(v___x_316_, v___x_319_);
v_bkt_321_ = lean_array_uget_borrowed(v_buckets_307_, v___x_320_);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_305_, v_bkt_321_);
if (v___x_322_ == 0)
{
return v_m_304_;
}
else
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_335_; 
lean_inc(v_bkt_321_);
lean_inc_ref(v_buckets_307_);
lean_inc(v_size_306_);
v_isSharedCheck_335_ = !lean_is_exclusive(v_m_304_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; lean_object* v_unused_337_; 
v_unused_336_ = lean_ctor_get(v_m_304_, 1);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_m_304_, 0);
lean_dec(v_unused_337_);
v___x_324_ = v_m_304_;
v_isShared_325_ = v_isSharedCheck_335_;
goto v_resetjp_323_;
}
else
{
lean_dec(v_m_304_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_335_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v_buckets_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_326_ = lean_box(0);
v_buckets_x27_327_ = lean_array_uset(v_buckets_307_, v___x_320_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_sub(v_size_306_, v___x_328_);
lean_dec(v_size_306_);
v___x_330_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_305_, v_bkt_321_);
v___x_331_ = lean_array_uset(v_buckets_x27_327_, v___x_320_, v___x_330_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_331_);
lean_ctor_set(v___x_324_, 0, v___x_329_);
v___x_333_ = v___x_324_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(lean_object* v_m_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_338_, v_a_339_);
lean_dec(v_a_339_);
return v_res_340_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t v_pu_341_, lean_object* v_lctx_342_, lean_object* v_param_343_){
_start:
{
if (v_pu_341_ == 0)
{
lean_object* v_paramsPure_344_; lean_object* v_paramsImpure_345_; lean_object* v_letDeclsPure_346_; lean_object* v_letDeclsImpure_347_; lean_object* v_funDeclsPure_348_; lean_object* v_funDeclsImpure_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_358_; 
v_paramsPure_344_ = lean_ctor_get(v_lctx_342_, 0);
v_paramsImpure_345_ = lean_ctor_get(v_lctx_342_, 1);
v_letDeclsPure_346_ = lean_ctor_get(v_lctx_342_, 2);
v_letDeclsImpure_347_ = lean_ctor_get(v_lctx_342_, 3);
v_funDeclsPure_348_ = lean_ctor_get(v_lctx_342_, 4);
v_funDeclsImpure_349_ = lean_ctor_get(v_lctx_342_, 5);
v_isSharedCheck_358_ = !lean_is_exclusive(v_lctx_342_);
if (v_isSharedCheck_358_ == 0)
{
v___x_351_ = v_lctx_342_;
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_funDeclsImpure_349_);
lean_inc(v_funDeclsPure_348_);
lean_inc(v_letDeclsImpure_347_);
lean_inc(v_letDeclsPure_346_);
lean_inc(v_paramsImpure_345_);
lean_inc(v_paramsPure_344_);
lean_dec(v_lctx_342_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_fvarId_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v_fvarId_353_ = lean_ctor_get(v_param_343_, 0);
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsPure_344_, v_fvarId_353_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_354_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_paramsImpure_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_letDeclsPure_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_letDeclsImpure_347_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_funDeclsPure_348_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v_funDeclsImpure_349_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_paramsPure_359_; lean_object* v_paramsImpure_360_; lean_object* v_letDeclsPure_361_; lean_object* v_letDeclsImpure_362_; lean_object* v_funDeclsPure_363_; lean_object* v_funDeclsImpure_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
v_paramsPure_359_ = lean_ctor_get(v_lctx_342_, 0);
v_paramsImpure_360_ = lean_ctor_get(v_lctx_342_, 1);
v_letDeclsPure_361_ = lean_ctor_get(v_lctx_342_, 2);
v_letDeclsImpure_362_ = lean_ctor_get(v_lctx_342_, 3);
v_funDeclsPure_363_ = lean_ctor_get(v_lctx_342_, 4);
v_funDeclsImpure_364_ = lean_ctor_get(v_lctx_342_, 5);
v_isSharedCheck_373_ = !lean_is_exclusive(v_lctx_342_);
if (v_isSharedCheck_373_ == 0)
{
v___x_366_ = v_lctx_342_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_funDeclsImpure_364_);
lean_inc(v_funDeclsPure_363_);
lean_inc(v_letDeclsImpure_362_);
lean_inc(v_letDeclsPure_361_);
lean_inc(v_paramsImpure_360_);
lean_inc(v_paramsPure_359_);
lean_dec(v_lctx_342_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_fvarId_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v_fvarId_368_ = lean_ctor_get(v_param_343_, 0);
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsImpure_360_, v_fvarId_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_paramsPure_359_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_letDeclsPure_361_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_letDeclsImpure_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_funDeclsPure_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_funDeclsImpure_364_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_eraseParam_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_341_ = stack[0].m_num;
lean_object* v_lctx_342_ = stack[1].m_obj;
lean_object* v_param_343_ = stack[2].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_341_, v_lctx_342_, v_param_343_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(lean_object* v_pu_375_, lean_object* v_lctx_376_, lean_object* v_param_377_){
_start:
{
uint8_t v_pu_boxed_378_; lean_object* v_res_379_; 
v_pu_boxed_378_ = lean_unbox(v_pu_375_);
v_res_379_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_boxed_378_, v_lctx_376_, v_param_377_);
lean_dec_ref(v_param_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(lean_object* v_00_u03b2_380_, lean_object* v_m_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_381_, v_a_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(lean_object* v_00_u03b2_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(v_00_u03b2_384_, v_m_385_, v_a_386_);
lean_dec(v_a_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(lean_object* v_00_u03b2_388_, lean_object* v_a_389_, lean_object* v_x_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_389_, v_x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_392_, lean_object* v_a_393_, lean_object* v_x_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(v_00_u03b2_392_, v_a_393_, v_x_394_);
lean_dec(v_a_393_);
return v_res_395_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(lean_object* v_as_396_, size_t v_i_397_, size_t v_stop_398_, lean_object* v_b_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_eq(v_i_397_, v_stop_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v_fvarId_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; 
v___x_401_ = lean_array_uget_borrowed(v_as_396_, v_i_397_);
v_fvarId_402_ = lean_ctor_get(v___x_401_, 0);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_b_399_, v_fvarId_402_);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_397_, v___x_404_);
v_i_397_ = v___x_405_;
v_b_399_ = v___x_403_;
goto _start;
}
else
{
return v_b_399_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_396_ = stack[0].m_obj;
size_t v_i_397_ = stack[1].m_num;
size_t v_stop_398_ = stack[2].m_num;
lean_object* v_b_399_ = stack[3].m_obj;
lean_object* v_res_407_;
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_as_396_, v_i_397_, v_stop_398_, v_b_399_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0___boxed(lean_object* v_as_408_, lean_object* v_i_409_, lean_object* v_stop_410_, lean_object* v_b_411_){
_start:
{
size_t v_i_boxed_412_; size_t v_stop_boxed_413_; lean_object* v_res_414_; 
v_i_boxed_412_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_stop_boxed_413_ = lean_unbox_usize(v_stop_410_);
lean_dec(v_stop_410_);
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_as_408_, v_i_boxed_412_, v_stop_boxed_413_, v_b_411_);
lean_dec_ref(v_as_408_);
return v_res_414_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t v_pu_415_, lean_object* v_lctx_416_, lean_object* v_ps_417_){
_start:
{
if (v_pu_415_ == 0)
{
lean_object* v_paramsPure_418_; lean_object* v_paramsImpure_419_; lean_object* v_letDeclsPure_420_; lean_object* v_letDeclsImpure_421_; lean_object* v_funDeclsPure_422_; lean_object* v_funDeclsImpure_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_paramsPure_418_ = lean_ctor_get(v_lctx_416_, 0);
v_paramsImpure_419_ = lean_ctor_get(v_lctx_416_, 1);
v_letDeclsPure_420_ = lean_ctor_get(v_lctx_416_, 2);
v_letDeclsImpure_421_ = lean_ctor_get(v_lctx_416_, 3);
v_funDeclsPure_422_ = lean_ctor_get(v_lctx_416_, 4);
v_funDeclsImpure_423_ = lean_ctor_get(v_lctx_416_, 5);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_array_get_size(v_ps_417_);
v___x_426_ = lean_nat_dec_lt(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
return v_lctx_416_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_le(v___x_425_, v___x_425_);
if (v___x_427_ == 0)
{
if (v___x_426_ == 0)
{
return v_lctx_416_;
}
else
{
lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
lean_inc_ref(v_funDeclsImpure_423_);
lean_inc_ref(v_funDeclsPure_422_);
lean_inc_ref(v_letDeclsImpure_421_);
lean_inc_ref(v_letDeclsPure_420_);
lean_inc_ref(v_paramsImpure_419_);
lean_inc_ref(v_paramsPure_418_);
v_isSharedCheck_437_ = !lean_is_exclusive(v_lctx_416_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; lean_object* v_unused_439_; lean_object* v_unused_440_; lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_438_ = lean_ctor_get(v_lctx_416_, 5);
lean_dec(v_unused_438_);
v_unused_439_ = lean_ctor_get(v_lctx_416_, 4);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_lctx_416_, 3);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_lctx_416_, 2);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_lctx_416_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_lctx_416_, 0);
lean_dec(v_unused_443_);
v___x_429_ = v_lctx_416_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_dec(v_lctx_416_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_431_ = ((size_t)0ULL);
v___x_432_ = lean_usize_of_nat(v___x_425_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_417_, v___x_431_, v___x_432_, v_paramsPure_418_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_433_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_paramsImpure_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_letDeclsPure_420_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_letDeclsImpure_421_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_funDeclsPure_422_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v_funDeclsImpure_423_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
lean_inc_ref(v_funDeclsImpure_423_);
lean_inc_ref(v_funDeclsPure_422_);
lean_inc_ref(v_letDeclsImpure_421_);
lean_inc_ref(v_letDeclsPure_420_);
lean_inc_ref(v_paramsImpure_419_);
lean_inc_ref(v_paramsPure_418_);
v_isSharedCheck_453_ = !lean_is_exclusive(v_lctx_416_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_454_ = lean_ctor_get(v_lctx_416_, 5);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_lctx_416_, 4);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_lctx_416_, 3);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_lctx_416_, 2);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_lctx_416_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_lctx_416_, 0);
lean_dec(v_unused_459_);
v___x_445_ = v_lctx_416_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_lctx_416_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_447_ = ((size_t)0ULL);
v___x_448_ = lean_usize_of_nat(v___x_425_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_417_, v___x_447_, v___x_448_, v_paramsPure_418_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_449_);
v___x_451_ = v___x_445_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_paramsImpure_419_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_letDeclsPure_420_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_letDeclsImpure_421_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_funDeclsPure_422_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_funDeclsImpure_423_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
else
{
lean_object* v_paramsPure_460_; lean_object* v_paramsImpure_461_; lean_object* v_letDeclsPure_462_; lean_object* v_letDeclsImpure_463_; lean_object* v_funDeclsPure_464_; lean_object* v_funDeclsImpure_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_paramsPure_460_ = lean_ctor_get(v_lctx_416_, 0);
v_paramsImpure_461_ = lean_ctor_get(v_lctx_416_, 1);
v_letDeclsPure_462_ = lean_ctor_get(v_lctx_416_, 2);
v_letDeclsImpure_463_ = lean_ctor_get(v_lctx_416_, 3);
v_funDeclsPure_464_ = lean_ctor_get(v_lctx_416_, 4);
v_funDeclsImpure_465_ = lean_ctor_get(v_lctx_416_, 5);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_array_get_size(v_ps_417_);
v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
return v_lctx_416_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = lean_nat_dec_le(v___x_467_, v___x_467_);
if (v___x_469_ == 0)
{
if (v___x_468_ == 0)
{
return v_lctx_416_;
}
else
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_479_; 
lean_inc_ref(v_funDeclsImpure_465_);
lean_inc_ref(v_funDeclsPure_464_);
lean_inc_ref(v_letDeclsImpure_463_);
lean_inc_ref(v_letDeclsPure_462_);
lean_inc_ref(v_paramsImpure_461_);
lean_inc_ref(v_paramsPure_460_);
v_isSharedCheck_479_ = !lean_is_exclusive(v_lctx_416_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; lean_object* v_unused_484_; lean_object* v_unused_485_; 
v_unused_480_ = lean_ctor_get(v_lctx_416_, 5);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_lctx_416_, 4);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_lctx_416_, 3);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_lctx_416_, 2);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_lctx_416_, 1);
lean_dec(v_unused_484_);
v_unused_485_ = lean_ctor_get(v_lctx_416_, 0);
lean_dec(v_unused_485_);
v___x_471_ = v_lctx_416_;
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
else
{
lean_dec(v_lctx_416_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_473_ = ((size_t)0ULL);
v___x_474_ = lean_usize_of_nat(v___x_467_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_417_, v___x_473_, v___x_474_, v_paramsImpure_461_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_475_);
v___x_477_ = v___x_471_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_paramsPure_460_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_letDeclsPure_462_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_letDeclsImpure_463_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_funDeclsPure_464_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_funDeclsImpure_465_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_495_; 
lean_inc_ref(v_funDeclsImpure_465_);
lean_inc_ref(v_funDeclsPure_464_);
lean_inc_ref(v_letDeclsImpure_463_);
lean_inc_ref(v_letDeclsPure_462_);
lean_inc_ref(v_paramsImpure_461_);
lean_inc_ref(v_paramsPure_460_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_lctx_416_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; 
v_unused_496_ = lean_ctor_get(v_lctx_416_, 5);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_lctx_416_, 4);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_lctx_416_, 3);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_lctx_416_, 2);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_lctx_416_, 1);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_lctx_416_, 0);
lean_dec(v_unused_501_);
v___x_487_ = v_lctx_416_;
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
else
{
lean_dec(v_lctx_416_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_467_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_417_, v___x_489_, v___x_490_, v_paramsImpure_461_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_491_);
v___x_493_ = v___x_487_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_paramsPure_460_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_letDeclsPure_462_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_letDeclsImpure_463_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_funDeclsPure_464_);
lean_ctor_set(v_reuseFailAlloc_494_, 5, v_funDeclsImpure_465_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_eraseParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_415_ = stack[0].m_num;
lean_object* v_lctx_416_ = stack[1].m_obj;
lean_object* v_ps_417_ = stack[2].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_415_, v_lctx_416_, v_ps_417_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(lean_object* v_pu_503_, lean_object* v_lctx_504_, lean_object* v_ps_505_){
_start:
{
uint8_t v_pu_boxed_506_; lean_object* v_res_507_; 
v_pu_boxed_506_ = lean_unbox(v_pu_503_);
v_res_507_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_boxed_506_, v_lctx_504_, v_ps_505_);
lean_dec_ref(v_ps_505_);
return v_res_507_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t v_pu_508_, lean_object* v_lctx_509_, lean_object* v_decl_510_){
_start:
{
if (v_pu_508_ == 0)
{
lean_object* v_paramsPure_511_; lean_object* v_paramsImpure_512_; lean_object* v_letDeclsPure_513_; lean_object* v_letDeclsImpure_514_; lean_object* v_funDeclsPure_515_; lean_object* v_funDeclsImpure_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_paramsPure_511_ = lean_ctor_get(v_lctx_509_, 0);
v_paramsImpure_512_ = lean_ctor_get(v_lctx_509_, 1);
v_letDeclsPure_513_ = lean_ctor_get(v_lctx_509_, 2);
v_letDeclsImpure_514_ = lean_ctor_get(v_lctx_509_, 3);
v_funDeclsPure_515_ = lean_ctor_get(v_lctx_509_, 4);
v_funDeclsImpure_516_ = lean_ctor_get(v_lctx_509_, 5);
v_isSharedCheck_525_ = !lean_is_exclusive(v_lctx_509_);
if (v_isSharedCheck_525_ == 0)
{
v___x_518_ = v_lctx_509_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_funDeclsImpure_516_);
lean_inc(v_funDeclsPure_515_);
lean_inc(v_letDeclsImpure_514_);
lean_inc(v_letDeclsPure_513_);
lean_inc(v_paramsImpure_512_);
lean_inc(v_paramsPure_511_);
lean_dec(v_lctx_509_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_fvarId_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v_fvarId_520_ = lean_ctor_get(v_decl_510_, 0);
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsPure_513_, v_fvarId_520_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 2, v___x_521_);
v___x_523_ = v___x_518_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_paramsPure_511_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_paramsImpure_512_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_letDeclsImpure_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_funDeclsPure_515_);
lean_ctor_set(v_reuseFailAlloc_524_, 5, v_funDeclsImpure_516_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v_paramsPure_526_; lean_object* v_paramsImpure_527_; lean_object* v_letDeclsPure_528_; lean_object* v_letDeclsImpure_529_; lean_object* v_funDeclsPure_530_; lean_object* v_funDeclsImpure_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
v_paramsPure_526_ = lean_ctor_get(v_lctx_509_, 0);
v_paramsImpure_527_ = lean_ctor_get(v_lctx_509_, 1);
v_letDeclsPure_528_ = lean_ctor_get(v_lctx_509_, 2);
v_letDeclsImpure_529_ = lean_ctor_get(v_lctx_509_, 3);
v_funDeclsPure_530_ = lean_ctor_get(v_lctx_509_, 4);
v_funDeclsImpure_531_ = lean_ctor_get(v_lctx_509_, 5);
v_isSharedCheck_540_ = !lean_is_exclusive(v_lctx_509_);
if (v_isSharedCheck_540_ == 0)
{
v___x_533_ = v_lctx_509_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_funDeclsImpure_531_);
lean_inc(v_funDeclsPure_530_);
lean_inc(v_letDeclsImpure_529_);
lean_inc(v_letDeclsPure_528_);
lean_inc(v_paramsImpure_527_);
lean_inc(v_paramsPure_526_);
lean_dec(v_lctx_509_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_fvarId_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v_fvarId_535_ = lean_ctor_get(v_decl_510_, 0);
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsImpure_529_, v_fvarId_535_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 3, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_paramsPure_526_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_paramsImpure_527_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_letDeclsPure_528_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v_funDeclsPure_530_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v_funDeclsImpure_531_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_eraseLetDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_508_ = stack[0].m_num;
lean_object* v_lctx_509_ = stack[1].m_obj;
lean_object* v_decl_510_ = stack[2].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_508_, v_lctx_509_, v_decl_510_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(lean_object* v_pu_542_, lean_object* v_lctx_543_, lean_object* v_decl_544_){
_start:
{
uint8_t v_pu_boxed_545_; lean_object* v_res_546_; 
v_pu_boxed_545_ = lean_unbox(v_pu_542_);
v_res_546_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_boxed_545_, v_lctx_543_, v_decl_544_);
lean_dec_ref(v_decl_544_);
return v_res_546_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t v_pu_547_, lean_object* v_lctx_548_, lean_object* v_decl_549_, uint8_t v_recursive_550_){
_start:
{
lean_object* v___y_552_; 
if (v_pu_547_ == 0)
{
lean_object* v_fvarId_557_; lean_object* v_paramsPure_558_; lean_object* v_paramsImpure_559_; lean_object* v_letDeclsPure_560_; lean_object* v_letDeclsImpure_561_; lean_object* v_funDeclsPure_562_; lean_object* v_funDeclsImpure_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
v_fvarId_557_ = lean_ctor_get(v_decl_549_, 0);
v_paramsPure_558_ = lean_ctor_get(v_lctx_548_, 0);
v_paramsImpure_559_ = lean_ctor_get(v_lctx_548_, 1);
v_letDeclsPure_560_ = lean_ctor_get(v_lctx_548_, 2);
v_letDeclsImpure_561_ = lean_ctor_get(v_lctx_548_, 3);
v_funDeclsPure_562_ = lean_ctor_get(v_lctx_548_, 4);
v_funDeclsImpure_563_ = lean_ctor_get(v_lctx_548_, 5);
v_isSharedCheck_571_ = !lean_is_exclusive(v_lctx_548_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v_lctx_548_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_funDeclsImpure_563_);
lean_inc(v_funDeclsPure_562_);
lean_inc(v_letDeclsImpure_561_);
lean_inc(v_letDeclsPure_560_);
lean_inc(v_paramsImpure_559_);
lean_inc(v_paramsPure_558_);
lean_dec(v_lctx_548_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsPure_562_, v_fvarId_557_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_paramsPure_558_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_paramsImpure_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_letDeclsPure_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_letDeclsImpure_561_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_funDeclsImpure_563_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v___y_552_ = v___x_569_;
goto v___jp_551_;
}
}
}
else
{
lean_object* v_fvarId_572_; lean_object* v_paramsPure_573_; lean_object* v_paramsImpure_574_; lean_object* v_letDeclsPure_575_; lean_object* v_letDeclsImpure_576_; lean_object* v_funDeclsPure_577_; lean_object* v_funDeclsImpure_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_fvarId_572_ = lean_ctor_get(v_decl_549_, 0);
v_paramsPure_573_ = lean_ctor_get(v_lctx_548_, 0);
v_paramsImpure_574_ = lean_ctor_get(v_lctx_548_, 1);
v_letDeclsPure_575_ = lean_ctor_get(v_lctx_548_, 2);
v_letDeclsImpure_576_ = lean_ctor_get(v_lctx_548_, 3);
v_funDeclsPure_577_ = lean_ctor_get(v_lctx_548_, 4);
v_funDeclsImpure_578_ = lean_ctor_get(v_lctx_548_, 5);
v_isSharedCheck_586_ = !lean_is_exclusive(v_lctx_548_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v_lctx_548_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_funDeclsImpure_578_);
lean_inc(v_funDeclsPure_577_);
lean_inc(v_letDeclsImpure_576_);
lean_inc(v_letDeclsPure_575_);
lean_inc(v_paramsImpure_574_);
lean_inc(v_paramsPure_573_);
lean_dec(v_lctx_548_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsImpure_578_, v_fvarId_572_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 5, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_paramsPure_573_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_paramsImpure_574_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_letDeclsPure_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_letDeclsImpure_576_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_funDeclsPure_577_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_552_ = v___x_584_;
goto v___jp_551_;
}
}
}
v___jp_551_:
{
if (v_recursive_550_ == 0)
{
return v___y_552_;
}
else
{
lean_object* v_params_553_; lean_object* v_value_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_params_553_ = lean_ctor_get(v_decl_549_, 2);
v_value_554_ = lean_ctor_get(v_decl_549_, 4);
v___x_555_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_547_, v___y_552_, v_params_553_);
v___x_556_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_547_, v_value_554_, v___x_555_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_eraseFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_547_ = stack[0].m_num;
lean_object* v_lctx_548_ = stack[1].m_obj;
lean_object* v_decl_549_ = stack[2].m_obj;
uint8_t v_recursive_550_ = stack[3].m_num;
lean_object* v_res_587_;
v_res_587_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_547_, v_lctx_548_, v_decl_549_, v_recursive_550_);
stack->m_obj
 = v_res_587_;
}
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t v_pu_588_, lean_object* v_code_589_, lean_object* v_lctx_590_){
_start:
{
switch(lean_obj_tag(v_code_589_))
{
case 0:
{
lean_object* v_decl_591_; lean_object* v_k_592_; lean_object* v___x_593_; 
v_decl_591_ = lean_ctor_get(v_code_589_, 0);
v_k_592_ = lean_ctor_get(v_code_589_, 1);
v___x_593_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_588_, v_lctx_590_, v_decl_591_);
v_code_589_ = v_k_592_;
v_lctx_590_ = v___x_593_;
goto _start;
}
case 1:
{
lean_object* v_decl_595_; lean_object* v_k_596_; uint8_t v___x_597_; lean_object* v___x_598_; 
v_decl_595_ = lean_ctor_get(v_code_589_, 0);
v_k_596_ = lean_ctor_get(v_code_589_, 1);
v___x_597_ = 1;
v___x_598_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_588_, v_lctx_590_, v_decl_595_, v___x_597_);
v_code_589_ = v_k_596_;
v_lctx_590_ = v___x_598_;
goto _start;
}
case 2:
{
lean_object* v_decl_600_; lean_object* v_k_601_; uint8_t v___x_602_; lean_object* v___x_603_; 
v_decl_600_ = lean_ctor_get(v_code_589_, 0);
v_k_601_ = lean_ctor_get(v_code_589_, 1);
v___x_602_ = 1;
v___x_603_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_588_, v_lctx_590_, v_decl_600_, v___x_602_);
v_code_589_ = v_k_601_;
v_lctx_590_ = v___x_603_;
goto _start;
}
case 4:
{
lean_object* v_cases_605_; lean_object* v_alts_606_; lean_object* v___x_607_; 
v_cases_605_ = lean_ctor_get(v_code_589_, 0);
v_alts_606_ = lean_ctor_get(v_cases_605_, 3);
v___x_607_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_588_, v_alts_606_, v_lctx_590_);
return v___x_607_;
}
case 7:
{
lean_object* v_k_608_; 
v_k_608_ = lean_ctor_get(v_code_589_, 3);
v_code_589_ = v_k_608_;
goto _start;
}
case 8:
{
lean_object* v_k_610_; 
v_k_610_ = lean_ctor_get(v_code_589_, 3);
v_code_589_ = v_k_610_;
goto _start;
}
case 9:
{
lean_object* v_k_612_; 
v_k_612_ = lean_ctor_get(v_code_589_, 5);
v_code_589_ = v_k_612_;
goto _start;
}
case 10:
{
lean_object* v_k_614_; 
v_k_614_ = lean_ctor_get(v_code_589_, 2);
v_code_589_ = v_k_614_;
goto _start;
}
case 11:
{
lean_object* v_k_616_; 
v_k_616_ = lean_ctor_get(v_code_589_, 2);
v_code_589_ = v_k_616_;
goto _start;
}
case 12:
{
lean_object* v_k_618_; 
v_k_618_ = lean_ctor_get(v_code_589_, 3);
v_code_589_ = v_k_618_;
goto _start;
}
case 13:
{
lean_object* v_k_620_; 
v_k_620_ = lean_ctor_get(v_code_589_, 1);
v_code_589_ = v_k_620_;
goto _start;
}
default: 
{
return v_lctx_590_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_eraseCode_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_588_ = stack[0].m_num;
lean_object* v_code_589_ = stack[1].m_obj;
lean_object* v_lctx_590_ = stack[2].m_obj;
lean_object* v_res_622_;
v_res_622_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_588_, v_code_589_, v_lctx_590_);
stack->m_obj
 = v_res_622_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(uint8_t v_pu_623_, lean_object* v_as_624_, size_t v_i_625_, size_t v_stop_626_, lean_object* v_b_627_){
_start:
{
lean_object* v___y_629_; uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_eq(v_i_625_, v_stop_626_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_array_uget_borrowed(v_as_624_, v_i_625_);
switch(lean_obj_tag(v___x_634_))
{
case 0:
{
lean_object* v_params_635_; lean_object* v_code_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_params_635_ = lean_ctor_get(v___x_634_, 1);
v_code_636_ = lean_ctor_get(v___x_634_, 2);
v___x_637_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_623_, v_b_627_, v_params_635_);
v___x_638_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_623_, v_code_636_, v___x_637_);
v___y_629_ = v___x_638_;
goto v___jp_628_;
}
case 1:
{
lean_object* v_code_639_; lean_object* v___x_640_; 
v_code_639_ = lean_ctor_get(v___x_634_, 1);
v___x_640_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_623_, v_code_639_, v_b_627_);
v___y_629_ = v___x_640_;
goto v___jp_628_;
}
default: 
{
lean_object* v_code_641_; lean_object* v___x_642_; 
v_code_641_ = lean_ctor_get(v___x_634_, 0);
v___x_642_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_623_, v_code_641_, v_b_627_);
v___y_629_ = v___x_642_;
goto v___jp_628_;
}
}
}
else
{
return v_b_627_;
}
v___jp_628_:
{
size_t v___x_630_; size_t v___x_631_; 
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_625_, v___x_630_);
v_i_625_ = v___x_631_;
v_b_627_ = v___y_629_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_623_ = stack[0].m_num;
lean_object* v_as_624_ = stack[1].m_obj;
size_t v_i_625_ = stack[2].m_num;
size_t v_stop_626_ = stack[3].m_num;
lean_object* v_b_627_ = stack[4].m_obj;
lean_object* v_res_643_;
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_623_, v_as_624_, v_i_625_, v_stop_626_, v_b_627_);
stack->m_obj
 = v_res_643_;
}
lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts(uint8_t v_pu_644_, lean_object* v_alts_645_, lean_object* v_lctx_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_array_get_size(v_alts_645_);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
return v_lctx_646_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_le(v___x_648_, v___x_648_);
if (v___x_650_ == 0)
{
if (v___x_649_ == 0)
{
return v_lctx_646_;
}
else
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_648_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_644_, v_alts_645_, v___x_651_, v___x_652_, v_lctx_646_);
return v___x_653_;
}
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_648_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_644_, v_alts_645_, v___x_654_, v___x_655_, v_lctx_646_);
return v___x_656_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_eraseAlts_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_644_ = stack[0].m_num;
lean_object* v_alts_645_ = stack[1].m_obj;
lean_object* v_lctx_646_ = stack[2].m_obj;
lean_object* v_res_657_;
v_res_657_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_644_, v_alts_645_, v_lctx_646_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(lean_object* v_pu_658_, lean_object* v_alts_659_, lean_object* v_lctx_660_){
_start:
{
uint8_t v_pu_boxed_661_; lean_object* v_res_662_; 
v_pu_boxed_661_ = lean_unbox(v_pu_658_);
v_res_662_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_boxed_661_, v_alts_659_, v_lctx_660_);
lean_dec_ref(v_alts_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(lean_object* v_pu_663_, lean_object* v_as_664_, lean_object* v_i_665_, lean_object* v_stop_666_, lean_object* v_b_667_){
_start:
{
uint8_t v_pu_boxed_668_; size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_pu_boxed_668_ = lean_unbox(v_pu_663_);
v_i_boxed_669_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_666_);
lean_dec(v_stop_666_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_boxed_668_, v_as_664_, v_i_boxed_669_, v_stop_boxed_670_, v_b_667_);
lean_dec_ref(v_as_664_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(lean_object* v_pu_672_, lean_object* v_lctx_673_, lean_object* v_decl_674_, lean_object* v_recursive_675_){
_start:
{
uint8_t v_pu_boxed_676_; uint8_t v_recursive_boxed_677_; lean_object* v_res_678_; 
v_pu_boxed_676_ = lean_unbox(v_pu_672_);
v_recursive_boxed_677_ = lean_unbox(v_recursive_675_);
v_res_678_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_boxed_676_, v_lctx_673_, v_decl_674_, v_recursive_boxed_677_);
lean_dec_ref(v_decl_674_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(lean_object* v_pu_679_, lean_object* v_code_680_, lean_object* v_lctx_681_){
_start:
{
uint8_t v_pu_boxed_682_; lean_object* v_res_683_; 
v_pu_boxed_682_ = lean_unbox(v_pu_679_);
v_res_683_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_boxed_682_, v_code_680_, v_lctx_681_);
lean_dec_ref(v_code_680_);
return v_res_683_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_params(lean_object* v_lctx_684_, uint8_t v_pu_685_){
_start:
{
if (v_pu_685_ == 0)
{
lean_object* v_paramsPure_686_; 
v_paramsPure_686_ = lean_ctor_get(v_lctx_684_, 0);
lean_inc_ref(v_paramsPure_686_);
return v_paramsPure_686_;
}
else
{
lean_object* v_paramsImpure_687_; 
v_paramsImpure_687_ = lean_ctor_get(v_lctx_684_, 1);
lean_inc_ref(v_paramsImpure_687_);
return v_paramsImpure_687_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_params_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_684_ = stack[0].m_obj;
uint8_t v_pu_685_ = stack[1].m_num;
lean_object* v_res_688_;
v_res_688_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_684_, v_pu_685_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params___boxed(lean_object* v_lctx_689_, lean_object* v_pu_690_){
_start:
{
uint8_t v_pu_boxed_691_; lean_object* v_res_692_; 
v_pu_boxed_691_ = lean_unbox(v_pu_690_);
v_res_692_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_689_, v_pu_boxed_691_);
lean_dec_ref(v_lctx_689_);
return v_res_692_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls(lean_object* v_lctx_693_, uint8_t v_pu_694_){
_start:
{
if (v_pu_694_ == 0)
{
lean_object* v_letDeclsPure_695_; 
v_letDeclsPure_695_ = lean_ctor_get(v_lctx_693_, 2);
lean_inc_ref(v_letDeclsPure_695_);
return v_letDeclsPure_695_;
}
else
{
lean_object* v_letDeclsImpure_696_; 
v_letDeclsImpure_696_ = lean_ctor_get(v_lctx_693_, 3);
lean_inc_ref(v_letDeclsImpure_696_);
return v_letDeclsImpure_696_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_letDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_693_ = stack[0].m_obj;
uint8_t v_pu_694_ = stack[1].m_num;
lean_object* v_res_697_;
v_res_697_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_693_, v_pu_694_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(lean_object* v_lctx_698_, lean_object* v_pu_699_){
_start:
{
uint8_t v_pu_boxed_700_; lean_object* v_res_701_; 
v_pu_boxed_700_ = lean_unbox(v_pu_699_);
v_res_701_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_698_, v_pu_boxed_700_);
lean_dec_ref(v_lctx_698_);
return v_res_701_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls(lean_object* v_lctx_702_, uint8_t v_pu_703_){
_start:
{
if (v_pu_703_ == 0)
{
lean_object* v_funDeclsPure_704_; 
v_funDeclsPure_704_ = lean_ctor_get(v_lctx_702_, 4);
lean_inc_ref(v_funDeclsPure_704_);
return v_funDeclsPure_704_;
}
else
{
lean_object* v_funDeclsImpure_705_; 
v_funDeclsImpure_705_ = lean_ctor_get(v_lctx_702_, 5);
lean_inc_ref(v_funDeclsImpure_705_);
return v_funDeclsImpure_705_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_funDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_702_ = stack[0].m_obj;
uint8_t v_pu_703_ = stack[1].m_num;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_702_, v_pu_703_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(lean_object* v_lctx_707_, lean_object* v_pu_708_){
_start:
{
uint8_t v_pu_boxed_709_; lean_object* v_res_710_; 
v_pu_boxed_709_ = lean_unbox(v_pu_708_);
v_res_710_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_707_, v_pu_boxed_709_);
lean_dec_ref(v_lctx_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
if (lean_obj_tag(v_a_711_) == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_a_712_);
return v___x_713_;
}
else
{
lean_object* v_value_714_; lean_object* v_tail_715_; lean_object* v_fvarId_716_; lean_object* v_binderName_717_; lean_object* v_type_718_; lean_object* v___x_719_; uint8_t v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_value_714_ = lean_ctor_get(v_a_711_, 1);
v_tail_715_ = lean_ctor_get(v_a_711_, 2);
v_fvarId_716_ = lean_ctor_get(v_value_714_, 0);
v_binderName_717_ = lean_ctor_get(v_value_714_, 1);
v_type_718_ = lean_ctor_get(v_value_714_, 3);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = 0;
v___x_721_ = 0;
lean_inc_ref(v_type_718_);
lean_inc(v_binderName_717_);
lean_inc(v_fvarId_716_);
v___x_722_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_722_, 0, v___x_719_);
lean_ctor_set(v___x_722_, 1, v_fvarId_716_);
lean_ctor_set(v___x_722_, 2, v_binderName_717_);
lean_ctor_set(v___x_722_, 3, v_type_718_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*4, v___x_720_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*4 + 1, v___x_721_);
v___x_723_ = l_Lean_LocalContext_addDecl(v_a_712_, v___x_722_);
v_a_711_ = v_tail_715_;
v_a_712_ = v___x_723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_725_, v_a_726_);
lean_dec(v_a_725_);
return v_res_727_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(lean_object* v_as_728_, size_t v_sz_729_, size_t v_i_730_, lean_object* v_b_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = lean_usize_dec_lt(v_i_730_, v_sz_729_);
if (v___x_732_ == 0)
{
return v_b_731_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_array_uget_borrowed(v_as_728_, v_i_730_);
v___x_734_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_733_, v_b_731_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
return v_a_735_;
}
else
{
lean_object* v_a_736_; size_t v___x_737_; size_t v___x_738_; 
v_a_736_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_734_, 1);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_730_, v___x_737_);
v_i_730_ = v___x_738_;
v_b_731_ = v_a_736_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_728_ = stack[0].m_obj;
size_t v_sz_729_ = stack[1].m_num;
size_t v_i_730_ = stack[2].m_num;
lean_object* v_b_731_ = stack[3].m_obj;
lean_object* v_res_740_;
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_as_728_, v_sz_729_, v_i_730_, v_b_731_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5___boxed(lean_object* v_as_741_, lean_object* v_sz_742_, lean_object* v_i_743_, lean_object* v_b_744_){
_start:
{
size_t v_sz_boxed_745_; size_t v_i_boxed_746_; lean_object* v_res_747_; 
v_sz_boxed_745_ = lean_unbox_usize(v_sz_742_);
lean_dec(v_sz_742_);
v_i_boxed_746_ = lean_unbox_usize(v_i_743_);
lean_dec(v_i_743_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_as_741_, v_sz_boxed_745_, v_i_boxed_746_, v_b_744_);
lean_dec_ref(v_as_741_);
return v_res_747_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(uint8_t v_pu_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
if (lean_obj_tag(v_a_749_) == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_a_750_);
return v___x_751_;
}
else
{
lean_object* v_value_752_; lean_object* v_tail_753_; lean_object* v_fvarId_754_; lean_object* v_binderName_755_; lean_object* v_type_756_; lean_object* v_value_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_value_752_ = lean_ctor_get(v_a_749_, 1);
lean_inc(v_value_752_);
v_tail_753_ = lean_ctor_get(v_a_749_, 2);
lean_inc(v_tail_753_);
lean_dec_ref_known(v_a_749_, 3);
v_fvarId_754_ = lean_ctor_get(v_value_752_, 0);
lean_inc(v_fvarId_754_);
v_binderName_755_ = lean_ctor_get(v_value_752_, 1);
lean_inc(v_binderName_755_);
v_type_756_ = lean_ctor_get(v_value_752_, 2);
lean_inc_ref(v_type_756_);
v_value_757_ = lean_ctor_get(v_value_752_, 3);
lean_inc(v_value_757_);
lean_dec(v_value_752_);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_748_, v_value_757_);
v___x_760_ = 1;
v___x_761_ = 0;
v___x_762_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_762_, 0, v___x_758_);
lean_ctor_set(v___x_762_, 1, v_fvarId_754_);
lean_ctor_set(v___x_762_, 2, v_binderName_755_);
lean_ctor_set(v___x_762_, 3, v_type_756_);
lean_ctor_set(v___x_762_, 4, v___x_759_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*5, v___x_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*5 + 1, v___x_761_);
v___x_763_ = l_Lean_LocalContext_addDecl(v_a_750_, v___x_762_);
v_a_749_ = v_tail_753_;
v_a_750_ = v___x_763_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_748_ = stack[0].m_num;
lean_object* v_a_749_ = stack[1].m_obj;
lean_object* v_a_750_ = stack[2].m_obj;
lean_object* v_res_765_;
v_res_765_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_748_, v_a_749_, v_a_750_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object* v_pu_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
uint8_t v_pu_boxed_769_; lean_object* v_res_770_; 
v_pu_boxed_769_ = lean_unbox(v_pu_766_);
v_res_770_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_boxed_769_, v_a_767_, v_a_768_);
return v_res_770_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(uint8_t v_pu_771_, lean_object* v_as_772_, size_t v_sz_773_, size_t v_i_774_, lean_object* v_b_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_lt(v_i_774_, v_sz_773_);
if (v___x_776_ == 0)
{
return v_b_775_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_array_uget_borrowed(v_as_772_, v_i_774_);
lean_inc(v_a_777_);
v___x_778_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_771_, v_a_777_, v_b_775_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
return v_a_779_;
}
else
{
lean_object* v_a_780_; size_t v___x_781_; size_t v___x_782_; 
v_a_780_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_778_, 1);
v___x_781_ = ((size_t)1ULL);
v___x_782_ = lean_usize_add(v_i_774_, v___x_781_);
v_i_774_ = v___x_782_;
v_b_775_ = v_a_780_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_771_ = stack[0].m_num;
lean_object* v_as_772_ = stack[1].m_obj;
size_t v_sz_773_ = stack[2].m_num;
size_t v_i_774_ = stack[3].m_num;
lean_object* v_b_775_ = stack[4].m_obj;
lean_object* v_res_784_;
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_771_, v_as_772_, v_sz_773_, v_i_774_, v_b_775_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4___boxed(lean_object* v_pu_785_, lean_object* v_as_786_, lean_object* v_sz_787_, lean_object* v_i_788_, lean_object* v_b_789_){
_start:
{
uint8_t v_pu_boxed_790_; size_t v_sz_boxed_791_; size_t v_i_boxed_792_; lean_object* v_res_793_; 
v_pu_boxed_790_ = lean_unbox(v_pu_785_);
v_sz_boxed_791_ = lean_unbox_usize(v_sz_787_);
lean_dec(v_sz_787_);
v_i_boxed_792_ = lean_unbox_usize(v_i_788_);
lean_dec(v_i_788_);
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_boxed_790_, v_as_786_, v_sz_boxed_791_, v_i_boxed_792_, v_b_789_);
lean_dec_ref(v_as_786_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
if (lean_obj_tag(v_a_794_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_a_795_);
return v___x_796_;
}
else
{
lean_object* v_value_797_; lean_object* v_tail_798_; lean_object* v_fvarId_799_; lean_object* v_binderName_800_; lean_object* v_type_801_; lean_object* v___x_802_; uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_value_797_ = lean_ctor_get(v_a_794_, 1);
v_tail_798_ = lean_ctor_get(v_a_794_, 2);
v_fvarId_799_ = lean_ctor_get(v_value_797_, 0);
v_binderName_800_ = lean_ctor_get(v_value_797_, 1);
v_type_801_ = lean_ctor_get(v_value_797_, 2);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = 0;
v___x_804_ = 0;
lean_inc_ref(v_type_801_);
lean_inc(v_binderName_800_);
lean_inc(v_fvarId_799_);
v___x_805_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_805_, 0, v___x_802_);
lean_ctor_set(v___x_805_, 1, v_fvarId_799_);
lean_ctor_set(v___x_805_, 2, v_binderName_800_);
lean_ctor_set(v___x_805_, 3, v_type_801_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*4, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*4 + 1, v___x_804_);
v___x_806_ = l_Lean_LocalContext_addDecl(v_a_795_, v___x_805_);
v_a_794_ = v_tail_798_;
v_a_795_ = v___x_806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_808_, v_a_809_);
lean_dec(v_a_808_);
return v_res_810_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(lean_object* v_as_811_, size_t v_sz_812_, size_t v_i_813_, lean_object* v_b_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_813_, v_sz_812_);
if (v___x_815_ == 0)
{
return v_b_814_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_817_; 
v_a_816_ = lean_array_uget_borrowed(v_as_811_, v_i_813_);
v___x_817_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_816_, v_b_814_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
return v_a_818_;
}
else
{
lean_object* v_a_819_; size_t v___x_820_; size_t v___x_821_; 
v_a_819_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_817_, 1);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_813_, v___x_820_);
v_i_813_ = v___x_821_;
v_b_814_ = v_a_819_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_811_ = stack[0].m_obj;
size_t v_sz_812_ = stack[1].m_num;
size_t v_i_813_ = stack[2].m_num;
lean_object* v_b_814_ = stack[3].m_obj;
lean_object* v_res_823_;
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_as_811_, v_sz_812_, v_i_813_, v_b_814_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3___boxed(lean_object* v_as_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_b_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_829_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_as_824_, v_sz_boxed_828_, v_i_boxed_829_, v_b_827_);
lean_dec_ref(v_as_824_);
return v_res_830_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0(void){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_unsigned_to_nat(32u);
v___x_835_ = lean_mk_empty_array_with_capacity(v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3(void){
_start:
{
size_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_837_ = ((size_t)5ULL);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_unsigned_to_nat(32u);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_839_);
v___x_841_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2);
v___x_842_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_838_);
lean_ctor_set(v___x_842_, 3, v___x_838_);
lean_ctor_set_usize(v___x_842_, 4, v___x_837_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_result_846_; 
v___x_843_ = lean_box(1);
v___x_844_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3);
v___x_845_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1);
v_result_846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_846_, 0, v___x_845_);
lean_ctor_set(v_result_846_, 1, v___x_844_);
lean_ctor_set(v_result_846_, 2, v___x_843_);
return v_result_846_;
}
}
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object* v_lctx_847_, uint8_t v_pu_848_){
_start:
{
lean_object* v___y_850_; size_t v___y_851_; lean_object* v___y_852_; size_t v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v_result_865_; lean_object* v___y_867_; 
v_result_865_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4);
if (v_pu_848_ == 0)
{
lean_object* v_paramsPure_874_; 
v_paramsPure_874_ = lean_ctor_get(v_lctx_847_, 0);
v___y_867_ = v_paramsPure_874_;
goto v___jp_866_;
}
else
{
lean_object* v_paramsImpure_875_; 
v_paramsImpure_875_ = lean_ctor_get(v_lctx_847_, 1);
v___y_867_ = v_paramsImpure_875_;
goto v___jp_866_;
}
v___jp_849_:
{
lean_object* v_buckets_853_; size_t v_sz_854_; lean_object* v___x_855_; 
v_buckets_853_ = lean_ctor_get(v___y_852_, 1);
v_sz_854_ = lean_array_size(v_buckets_853_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_buckets_853_, v_sz_854_, v___y_851_, v___y_850_);
return v___x_855_;
}
v___jp_856_:
{
lean_object* v_buckets_860_; size_t v_sz_861_; lean_object* v___x_862_; 
v_buckets_860_ = lean_ctor_get(v___y_859_, 1);
v_sz_861_ = lean_array_size(v_buckets_860_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_848_, v_buckets_860_, v_sz_861_, v___y_857_, v___y_858_);
if (v_pu_848_ == 0)
{
lean_object* v_funDeclsPure_863_; 
v_funDeclsPure_863_ = lean_ctor_get(v_lctx_847_, 4);
v___y_850_ = v___x_862_;
v___y_851_ = v___y_857_;
v___y_852_ = v_funDeclsPure_863_;
goto v___jp_849_;
}
else
{
lean_object* v_funDeclsImpure_864_; 
v_funDeclsImpure_864_ = lean_ctor_get(v_lctx_847_, 5);
v___y_850_ = v___x_862_;
v___y_851_ = v___y_857_;
v___y_852_ = v_funDeclsImpure_864_;
goto v___jp_849_;
}
}
v___jp_866_:
{
lean_object* v_buckets_868_; size_t v_sz_869_; size_t v___x_870_; lean_object* v___x_871_; 
v_buckets_868_ = lean_ctor_get(v___y_867_, 1);
v_sz_869_ = lean_array_size(v_buckets_868_);
v___x_870_ = ((size_t)0ULL);
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_buckets_868_, v_sz_869_, v___x_870_, v_result_865_);
if (v_pu_848_ == 0)
{
lean_object* v_letDeclsPure_872_; 
v_letDeclsPure_872_ = lean_ctor_get(v_lctx_847_, 2);
v___y_857_ = v___x_870_;
v___y_858_ = v___x_871_;
v___y_859_ = v_letDeclsPure_872_;
goto v___jp_856_;
}
else
{
lean_object* v_letDeclsImpure_873_; 
v_letDeclsImpure_873_ = lean_ctor_get(v_lctx_847_, 3);
v___y_857_ = v___x_870_;
v___y_858_ = v___x_871_;
v___y_859_ = v_letDeclsImpure_873_;
goto v___jp_856_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LCtx_toLocalContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_847_ = stack[0].m_obj;
uint8_t v_pu_848_ = stack[1].m_num;
lean_object* v_res_876_;
v_res_876_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_847_, v_pu_848_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(lean_object* v_lctx_877_, lean_object* v_pu_878_){
_start:
{
uint8_t v_pu_boxed_879_; lean_object* v_res_880_; 
v_pu_boxed_879_ = lean_unbox(v_pu_878_);
v_res_880_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_877_, v_pu_boxed_879_);
lean_dec_ref(v_lctx_877_);
return v_res_880_;
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
