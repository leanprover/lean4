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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLCtx;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object*, lean_object*);
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
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2);
v___x_10_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_ctor_set(v___x_10_, 2, v___x_9_);
lean_ctor_set(v___x_10_, 3, v___x_9_);
lean_ctor_set(v___x_10_, 4, v___x_9_);
lean_ctor_set(v___x_10_, 5, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__3, &l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__3_once, _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__3);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLCtx(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(lean_object* v_m_13_, lean_object* v_query_14_, lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_zero_18_; uint8_t v_isZero_19_; 
v_zero_18_ = lean_unsigned_to_nat(0u);
v_isZero_19_ = lean_nat_dec_eq(v_x_16_, v_zero_18_);
if (v_isZero_19_ == 1)
{
lean_dec(v_x_17_);
lean_dec(v_x_16_);
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(2);
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
v_val_21_ = lean_ctor_get(v_x_15_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v_x_15_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_val_21_);
lean_dec(v_x_15_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_val_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_keyArray_29_; lean_object* v_valueArray_30_; lean_object* v___x_31_; uint8_t v_isSome_32_; 
v_keyArray_29_ = lean_ctor_get(v_m_13_, 1);
v_valueArray_30_ = lean_ctor_get(v_m_13_, 2);
v___x_31_ = lean_array_fget_borrowed(v_keyArray_29_, v_x_17_);
v_isSome_32_ = lean_noption_is_some(v___x_31_);
if (v_isSome_32_ == 0)
{
lean_dec(v_x_16_);
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_x_17_);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_dec(v_x_17_);
v_val_34_ = lean_ctor_get(v_x_15_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v_x_15_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_val_34_);
lean_dec(v_x_15_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_val_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
else
{
lean_object* v_one_42_; lean_object* v_n_43_; lean_object* v___y_45_; 
v_one_42_ = lean_unsigned_to_nat(1u);
v_n_43_ = lean_nat_sub(v_x_16_, v_one_42_);
lean_dec(v_x_16_);
if (v_isSome_32_ == 0)
{
goto v___jp_51_;
}
else
{
lean_object* v___x_53_; uint8_t v_isSome_54_; 
v___x_53_ = lean_array_fget_borrowed(v_valueArray_30_, v_x_17_);
v_isSome_54_ = lean_noption_is_some(v___x_53_);
if (v_isSome_54_ == 0)
{
goto v___jp_51_;
}
else
{
lean_object* v_val_55_; uint8_t v___x_56_; 
lean_inc(v___x_31_);
v_val_55_ = lean_noption_get(v___x_31_);
v___x_56_ = l_Lean_instBEqFVarId_beq(v_val_55_, v_query_14_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
lean_dec(v_val_55_);
v___x_57_ = lean_array_get_size(v_keyArray_29_);
v___x_58_ = lean_nat_add(v_x_17_, v_one_42_);
lean_dec(v_x_17_);
v___x_59_ = lean_nat_dec_lt(v___x_58_, v___x_57_);
if (v___x_59_ == 0)
{
lean_dec(v___x_58_);
v_x_16_ = v_n_43_;
v_x_17_ = v_zero_18_;
goto _start;
}
else
{
v_x_16_ = v_n_43_;
v_x_17_ = v___x_58_;
goto _start;
}
}
else
{
lean_object* v_val_62_; lean_object* v___x_63_; 
lean_dec(v_n_43_);
lean_dec(v_x_15_);
lean_inc(v___x_53_);
v_val_62_ = lean_noption_get(v___x_53_);
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v_x_17_);
lean_ctor_set(v___x_63_, 1, v_val_55_);
lean_ctor_set(v___x_63_, 2, v_val_62_);
return v___x_63_;
}
}
}
v___jp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_array_get_size(v_keyArray_29_);
v___x_47_ = lean_nat_add(v_x_17_, v_one_42_);
lean_dec(v_x_17_);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v___x_46_);
if (v___x_48_ == 0)
{
lean_dec(v___x_47_);
v_x_15_ = v___y_45_;
v_x_16_ = v_n_43_;
v_x_17_ = v_zero_18_;
goto _start;
}
else
{
v_x_15_ = v___y_45_;
v_x_16_ = v_n_43_;
v_x_17_ = v___x_47_;
goto _start;
}
}
v___jp_51_:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_52_; 
lean_inc(v_x_17_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_x_17_);
v___y_45_ = v___x_52_;
goto v___jp_44_;
}
else
{
v___y_45_ = v_x_15_;
goto v___jp_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg___boxed(lean_object* v_m_64_, lean_object* v_query_65_, lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_m_64_, v_query_65_, v_x_66_, v_x_67_, v_x_68_);
lean_dec(v_query_65_);
lean_dec_ref(v_m_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object* v_m_70_, lean_object* v_query_71_){
_start:
{
lean_object* v_keyArray_72_; lean_object* v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v_fold_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_keyArray_72_ = lean_ctor_get(v_m_70_, 1);
v___x_73_ = lean_array_get_size(v_keyArray_72_);
v___x_74_ = l_Lean_instHashableFVarId_hash(v_query_71_);
v___x_75_ = 32ULL;
v___x_76_ = lean_uint64_shift_right(v___x_74_, v___x_75_);
v_fold_77_ = lean_uint64_xor(v___x_74_, v___x_76_);
v___x_78_ = 16ULL;
v___x_79_ = lean_uint64_shift_right(v_fold_77_, v___x_78_);
v___x_80_ = lean_uint64_xor(v_fold_77_, v___x_79_);
v___x_81_ = lean_uint64_to_usize(v___x_80_);
v___x_82_ = lean_usize_of_nat(v___x_73_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_sub(v___x_82_, v___x_83_);
v___x_85_ = lean_usize_land(v___x_81_, v___x_84_);
v___x_86_ = lean_usize_to_nat(v___x_85_);
v___x_87_ = lean_box(0);
v___x_88_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_m_70_, v_query_71_, v___x_87_, v___x_73_, v___x_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg___boxed(lean_object* v_m_89_, lean_object* v_query_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_89_, v_query_90_);
lean_dec(v_query_90_);
lean_dec_ref(v_m_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg(lean_object* v_b_92_, lean_object* v_acc_93_, lean_object* v_i_94_){
_start:
{
lean_object* v___y_96_; lean_object* v_keyArray_104_; lean_object* v_valueArray_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_keyArray_104_ = lean_ctor_get(v_b_92_, 1);
v_valueArray_105_ = lean_ctor_get(v_b_92_, 2);
v___x_106_ = lean_array_get_size(v_keyArray_104_);
v___x_107_ = lean_nat_dec_lt(v_i_94_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec(v_i_94_);
return v_acc_93_;
}
else
{
lean_object* v___x_108_; uint8_t v_isSome_109_; 
v___x_108_ = lean_array_fget_borrowed(v_keyArray_104_, v_i_94_);
v_isSome_109_ = lean_noption_is_some(v___x_108_);
if (v_isSome_109_ == 0)
{
goto v___jp_100_;
}
else
{
lean_object* v___x_110_; uint8_t v_isSome_111_; 
v___x_110_ = lean_array_fget_borrowed(v_valueArray_105_, v_i_94_);
v_isSome_111_ = lean_noption_is_some(v___x_110_);
if (v_isSome_111_ == 0)
{
goto v___jp_100_;
}
else
{
lean_object* v_val_112_; lean_object* v_val_113_; lean_object* v_i_115_; lean_object* v___x_120_; 
lean_inc(v___x_108_);
v_val_112_ = lean_noption_get(v___x_108_);
lean_inc(v___x_110_);
v_val_113_ = lean_noption_get(v___x_110_);
v___x_120_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_acc_93_, v_val_112_);
switch(lean_obj_tag(v___x_120_))
{
case 0:
{
lean_object* v_index_121_; lean_object* v_size_122_; lean_object* v___x_123_; 
v_index_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_index_121_);
lean_dec_ref_known(v___x_120_, 3);
v_size_122_ = lean_ctor_get(v_acc_93_, 0);
lean_inc(v_size_122_);
v___x_123_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_93_, v_size_122_, v_index_121_, v_val_112_, v_val_113_);
lean_dec(v_index_121_);
v___y_96_ = v___x_123_;
goto v___jp_95_;
}
case 1:
{
lean_object* v_index_124_; 
v_index_124_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_index_124_);
lean_dec_ref_known(v___x_120_, 1);
v_i_115_ = v_index_124_;
goto v___jp_114_;
}
default: 
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_93_, v___x_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_index_127_; 
v_index_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_index_127_);
lean_dec_ref_known(v___x_126_, 1);
v_i_115_ = v_index_127_;
goto v___jp_114_;
}
else
{
lean_dec(v_val_113_);
lean_dec(v_val_112_);
v___y_96_ = v_acc_93_;
goto v___jp_95_;
}
}
}
v___jp_114_:
{
lean_object* v_size_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_size_116_ = lean_ctor_get(v_acc_93_, 0);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_size_116_, v___x_117_);
v___x_119_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_93_, v___x_118_, v_i_115_, v_val_112_, v_val_113_);
lean_dec(v_i_115_);
v___y_96_ = v___x_119_;
goto v___jp_95_;
}
}
}
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_i_94_, v___x_97_);
lean_dec(v_i_94_);
v_acc_93_ = v___y_96_;
v_i_94_ = v___x_98_;
goto _start;
}
v___jp_100_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_i_94_, v___x_101_);
lean_dec(v_i_94_);
v_i_94_ = v___x_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_128_, lean_object* v_acc_129_, lean_object* v_i_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg(v_b_128_, v_acc_129_, v_i_130_);
lean_dec_ref(v_b_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg(lean_object* v_init_132_, lean_object* v_b_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg(v_b_133_, v_init_132_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg___boxed(lean_object* v_init_136_, lean_object* v_b_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg(v_init_136_, v_b_137_);
lean_dec_ref(v_b_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(lean_object* v_m_139_){
_start:
{
lean_object* v_keyArray_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_cellCount_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_target_147_; lean_object* v___x_148_; 
v_keyArray_140_ = lean_ctor_get(v_m_139_, 1);
v___x_141_ = lean_array_get_size(v_keyArray_140_);
v___x_142_ = lean_unsigned_to_nat(2u);
v_cellCount_143_ = lean_nat_mul(v___x_141_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_143_);
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_143_);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_143_);
v_target_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_147_, 0, v___x_144_);
lean_ctor_set(v_target_147_, 1, v___x_145_);
lean_ctor_set(v_target_147_, 2, v___x_146_);
v___x_148_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg(v_target_147_, v_m_139_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg___boxed(lean_object* v_m_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_m_149_);
lean_dec_ref(v_m_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t v_pu_151_, lean_object* v_lctx_152_, lean_object* v_param_153_){
_start:
{
if (v_pu_151_ == 0)
{
lean_object* v_paramsPure_154_; lean_object* v_paramsImpure_155_; lean_object* v_letDeclsPure_156_; lean_object* v_letDeclsImpure_157_; lean_object* v_funDeclsPure_158_; lean_object* v_funDeclsImpure_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_238_; 
v_paramsPure_154_ = lean_ctor_get(v_lctx_152_, 0);
v_paramsImpure_155_ = lean_ctor_get(v_lctx_152_, 1);
v_letDeclsPure_156_ = lean_ctor_get(v_lctx_152_, 2);
v_letDeclsImpure_157_ = lean_ctor_get(v_lctx_152_, 3);
v_funDeclsPure_158_ = lean_ctor_get(v_lctx_152_, 4);
v_funDeclsImpure_159_ = lean_ctor_get(v_lctx_152_, 5);
v_isSharedCheck_238_ = !lean_is_exclusive(v_lctx_152_);
if (v_isSharedCheck_238_ == 0)
{
v___x_161_ = v_lctx_152_;
v_isShared_162_ = v_isSharedCheck_238_;
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
lean_dec(v_lctx_152_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_238_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_fvarId_163_; lean_object* v___y_165_; lean_object* v_i_166_; lean_object* v___y_175_; lean_object* v___y_187_; lean_object* v_i_188_; lean_object* v___x_206_; 
v_fvarId_163_ = lean_ctor_get(v_param_153_, 0);
lean_inc(v_fvarId_163_);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsPure_154_, v_fvarId_163_);
switch(lean_obj_tag(v___x_206_))
{
case 0:
{
lean_object* v_index_207_; lean_object* v_size_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_del_object(v___x_161_);
v_index_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_index_207_);
lean_dec_ref_known(v___x_206_, 3);
v_size_208_ = lean_ctor_get(v_paramsPure_154_, 0);
lean_inc(v_size_208_);
v___x_209_ = l_Std_DHashMap_Raw_setEntry___redArg(v_paramsPure_154_, v_size_208_, v_index_207_, v_fvarId_163_, v_param_153_);
lean_dec(v_index_207_);
v___x_210_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_210_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_210_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_210_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_210_, 5, v_funDeclsImpure_159_);
return v___x_210_;
}
case 1:
{
lean_object* v_index_211_; lean_object* v_size_212_; lean_object* v_keyArray_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
lean_del_object(v___x_161_);
v_index_211_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_206_, 1);
v_size_212_ = lean_ctor_get(v_paramsPure_154_, 0);
v_keyArray_213_ = lean_ctor_get(v_paramsPure_154_, 1);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_size_212_, v___x_214_);
v___x_216_ = lean_array_get_size(v_keyArray_213_);
v___x_217_ = lean_nat_dec_lt(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v___x_215_);
lean_dec(v_index_211_);
goto v___jp_194_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_218_ = lean_unsigned_to_nat(4u);
v___x_219_ = lean_nat_mul(v___x_215_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(3u);
v___x_221_ = lean_nat_mul(v___x_216_, v___x_220_);
v___x_222_ = lean_nat_dec_le(v___x_219_, v___x_221_);
lean_dec(v___x_221_);
lean_dec(v___x_219_);
if (v___x_222_ == 0)
{
lean_dec(v___x_215_);
lean_dec(v_index_211_);
goto v___jp_194_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = l_Std_DHashMap_Raw_setEntry___redArg(v_paramsPure_154_, v___x_215_, v_index_211_, v_fvarId_163_, v_param_153_);
lean_dec(v_index_211_);
v___x_224_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_224_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_224_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_224_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_224_, 5, v_funDeclsImpure_159_);
return v___x_224_;
}
}
}
default: 
{
lean_object* v_size_225_; lean_object* v_keyArray_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_size_225_ = lean_ctor_get(v_paramsPure_154_, 0);
v_keyArray_226_ = lean_ctor_get(v_paramsPure_154_, 1);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_size_225_, v___x_227_);
v___x_229_ = lean_array_get_size(v_keyArray_226_);
v___x_230_ = lean_nat_dec_lt(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_dec(v___x_228_);
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_paramsPure_154_);
lean_dec_ref(v_paramsPure_154_);
v___y_175_ = v___x_231_;
goto v___jp_174_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_232_ = lean_unsigned_to_nat(4u);
v___x_233_ = lean_nat_mul(v___x_228_, v___x_232_);
lean_dec(v___x_228_);
v___x_234_ = lean_unsigned_to_nat(3u);
v___x_235_ = lean_nat_mul(v___x_229_, v___x_234_);
v___x_236_ = lean_nat_dec_le(v___x_233_, v___x_235_);
lean_dec(v___x_235_);
lean_dec(v___x_233_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_paramsPure_154_);
lean_dec_ref(v_paramsPure_154_);
v___y_175_ = v___x_237_;
goto v___jp_174_;
}
else
{
v___y_175_ = v_paramsPure_154_;
goto v___jp_174_;
}
}
}
}
v___jp_164_:
{
lean_object* v_size_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v_size_167_ = lean_ctor_get(v___y_165_, 0);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v_size_167_, v___x_168_);
v___x_170_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_165_, v___x_169_, v_i_166_, v_fvarId_163_, v_param_153_);
lean_dec(v_i_166_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_170_);
v___x_172_ = v___x_161_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_paramsImpure_155_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_letDeclsPure_156_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_funDeclsPure_158_);
lean_ctor_set(v_reuseFailAlloc_173_, 5, v_funDeclsImpure_159_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
v___jp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___y_175_, v_fvarId_163_);
switch(lean_obj_tag(v___x_176_))
{
case 0:
{
lean_object* v_index_177_; lean_object* v_size_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_del_object(v___x_161_);
v_index_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_177_);
lean_dec_ref_known(v___x_176_, 3);
v_size_178_ = lean_ctor_get(v___y_175_, 0);
lean_inc(v_size_178_);
v___x_179_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_175_, v_size_178_, v_index_177_, v_fvarId_163_, v_param_153_);
lean_dec(v_index_177_);
v___x_180_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_180_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_180_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_180_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_180_, 5, v_funDeclsImpure_159_);
return v___x_180_;
}
case 1:
{
lean_object* v_index_181_; 
v_index_181_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_181_);
lean_dec_ref_known(v___x_176_, 1);
v___y_165_ = v___y_175_;
v_i_166_ = v_index_181_;
goto v___jp_164_;
}
default: 
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_175_, v___x_182_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_index_184_; 
v_index_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_index_184_);
lean_dec_ref_known(v___x_183_, 1);
v___y_165_ = v___y_175_;
v_i_166_ = v_index_184_;
goto v___jp_164_;
}
else
{
lean_object* v___x_185_; 
lean_dec(v_fvarId_163_);
lean_del_object(v___x_161_);
lean_dec_ref(v_param_153_);
v___x_185_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_185_, 0, v___y_175_);
lean_ctor_set(v___x_185_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_185_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_185_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_185_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_185_, 5, v_funDeclsImpure_159_);
return v___x_185_;
}
}
}
}
v___jp_186_:
{
lean_object* v_size_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_size_189_ = lean_ctor_get(v___y_187_, 0);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_size_189_, v___x_190_);
v___x_192_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_187_, v___x_191_, v_i_188_, v_fvarId_163_, v_param_153_);
lean_dec(v_i_188_);
v___x_193_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_193_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_193_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_193_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_193_, 5, v_funDeclsImpure_159_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_paramsPure_154_);
lean_dec_ref(v_paramsPure_154_);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___x_195_, v_fvarId_163_);
switch(lean_obj_tag(v___x_196_))
{
case 0:
{
lean_object* v_index_197_; lean_object* v_size_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_index_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_196_, 3);
v_size_198_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_size_198_);
v___x_199_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_195_, v_size_198_, v_index_197_, v_fvarId_163_, v_param_153_);
lean_dec(v_index_197_);
v___x_200_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_200_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_200_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_200_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_200_, 5, v_funDeclsImpure_159_);
return v___x_200_;
}
case 1:
{
lean_object* v_index_201_; 
v_index_201_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_201_);
lean_dec_ref_known(v___x_196_, 1);
v___y_187_ = v___x_195_;
v_i_188_ = v_index_201_;
goto v___jp_186_;
}
default: 
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_195_, v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_index_204_; 
v_index_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_index_204_);
lean_dec_ref_known(v___x_203_, 1);
v___y_187_ = v___x_195_;
v_i_188_ = v_index_204_;
goto v___jp_186_;
}
else
{
lean_object* v___x_205_; 
lean_dec(v_fvarId_163_);
lean_dec_ref(v_param_153_);
v___x_205_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_205_, 0, v___x_195_);
lean_ctor_set(v___x_205_, 1, v_paramsImpure_155_);
lean_ctor_set(v___x_205_, 2, v_letDeclsPure_156_);
lean_ctor_set(v___x_205_, 3, v_letDeclsImpure_157_);
lean_ctor_set(v___x_205_, 4, v_funDeclsPure_158_);
lean_ctor_set(v___x_205_, 5, v_funDeclsImpure_159_);
return v___x_205_;
}
}
}
}
}
}
else
{
lean_object* v_paramsPure_239_; lean_object* v_paramsImpure_240_; lean_object* v_letDeclsPure_241_; lean_object* v_letDeclsImpure_242_; lean_object* v_funDeclsPure_243_; lean_object* v_funDeclsImpure_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_323_; 
v_paramsPure_239_ = lean_ctor_get(v_lctx_152_, 0);
v_paramsImpure_240_ = lean_ctor_get(v_lctx_152_, 1);
v_letDeclsPure_241_ = lean_ctor_get(v_lctx_152_, 2);
v_letDeclsImpure_242_ = lean_ctor_get(v_lctx_152_, 3);
v_funDeclsPure_243_ = lean_ctor_get(v_lctx_152_, 4);
v_funDeclsImpure_244_ = lean_ctor_get(v_lctx_152_, 5);
v_isSharedCheck_323_ = !lean_is_exclusive(v_lctx_152_);
if (v_isSharedCheck_323_ == 0)
{
v___x_246_ = v_lctx_152_;
v_isShared_247_ = v_isSharedCheck_323_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_funDeclsImpure_244_);
lean_inc(v_funDeclsPure_243_);
lean_inc(v_letDeclsImpure_242_);
lean_inc(v_letDeclsPure_241_);
lean_inc(v_paramsImpure_240_);
lean_inc(v_paramsPure_239_);
lean_dec(v_lctx_152_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_323_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_fvarId_248_; lean_object* v___y_250_; lean_object* v_i_251_; lean_object* v___y_260_; lean_object* v___y_272_; lean_object* v_i_273_; lean_object* v___x_291_; 
v_fvarId_248_ = lean_ctor_get(v_param_153_, 0);
lean_inc(v_fvarId_248_);
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsImpure_240_, v_fvarId_248_);
switch(lean_obj_tag(v___x_291_))
{
case 0:
{
lean_object* v_index_292_; lean_object* v_size_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_del_object(v___x_246_);
v_index_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_292_);
lean_dec_ref_known(v___x_291_, 3);
v_size_293_ = lean_ctor_get(v_paramsImpure_240_, 0);
lean_inc(v_size_293_);
v___x_294_ = l_Std_DHashMap_Raw_setEntry___redArg(v_paramsImpure_240_, v_size_293_, v_index_292_, v_fvarId_248_, v_param_153_);
lean_dec(v_index_292_);
v___x_295_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_295_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_ctor_set(v___x_295_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_295_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_295_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_295_, 5, v_funDeclsImpure_244_);
return v___x_295_;
}
case 1:
{
lean_object* v_index_296_; lean_object* v_size_297_; lean_object* v_keyArray_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
lean_del_object(v___x_246_);
v_index_296_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_296_);
lean_dec_ref_known(v___x_291_, 1);
v_size_297_ = lean_ctor_get(v_paramsImpure_240_, 0);
v_keyArray_298_ = lean_ctor_get(v_paramsImpure_240_, 1);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_size_297_, v___x_299_);
v___x_301_ = lean_array_get_size(v_keyArray_298_);
v___x_302_ = lean_nat_dec_lt(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v___x_300_);
lean_dec(v_index_296_);
goto v___jp_279_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_303_ = lean_unsigned_to_nat(4u);
v___x_304_ = lean_nat_mul(v___x_300_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(3u);
v___x_306_ = lean_nat_mul(v___x_301_, v___x_305_);
v___x_307_ = lean_nat_dec_le(v___x_304_, v___x_306_);
lean_dec(v___x_306_);
lean_dec(v___x_304_);
if (v___x_307_ == 0)
{
lean_dec(v___x_300_);
lean_dec(v_index_296_);
goto v___jp_279_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Std_DHashMap_Raw_setEntry___redArg(v_paramsImpure_240_, v___x_300_, v_index_296_, v_fvarId_248_, v_param_153_);
lean_dec(v_index_296_);
v___x_309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_309_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_ctor_set(v___x_309_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_309_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_309_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_309_, 5, v_funDeclsImpure_244_);
return v___x_309_;
}
}
}
default: 
{
lean_object* v_size_310_; lean_object* v_keyArray_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_size_310_ = lean_ctor_get(v_paramsImpure_240_, 0);
v_keyArray_311_ = lean_ctor_get(v_paramsImpure_240_, 1);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_size_310_, v___x_312_);
v___x_314_ = lean_array_get_size(v_keyArray_311_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v___x_313_);
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_paramsImpure_240_);
lean_dec_ref(v_paramsImpure_240_);
v___y_260_ = v___x_316_;
goto v___jp_259_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_317_ = lean_unsigned_to_nat(4u);
v___x_318_ = lean_nat_mul(v___x_313_, v___x_317_);
lean_dec(v___x_313_);
v___x_319_ = lean_unsigned_to_nat(3u);
v___x_320_ = lean_nat_mul(v___x_314_, v___x_319_);
v___x_321_ = lean_nat_dec_le(v___x_318_, v___x_320_);
lean_dec(v___x_320_);
lean_dec(v___x_318_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_paramsImpure_240_);
lean_dec_ref(v_paramsImpure_240_);
v___y_260_ = v___x_322_;
goto v___jp_259_;
}
else
{
v___y_260_ = v_paramsImpure_240_;
goto v___jp_259_;
}
}
}
}
v___jp_249_:
{
lean_object* v_size_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v_size_252_ = lean_ctor_get(v___y_250_, 0);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_size_252_, v___x_253_);
v___x_255_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_250_, v___x_254_, v_i_251_, v_fvarId_248_, v_param_153_);
lean_dec(v_i_251_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_255_);
v___x_257_ = v___x_246_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_paramsPure_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_letDeclsPure_241_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_funDeclsPure_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 5, v_funDeclsImpure_244_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
v___jp_259_:
{
lean_object* v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___y_260_, v_fvarId_248_);
switch(lean_obj_tag(v___x_261_))
{
case 0:
{
lean_object* v_index_262_; lean_object* v_size_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_del_object(v___x_246_);
v_index_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_index_262_);
lean_dec_ref_known(v___x_261_, 3);
v_size_263_ = lean_ctor_get(v___y_260_, 0);
lean_inc(v_size_263_);
v___x_264_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_260_, v_size_263_, v_index_262_, v_fvarId_248_, v_param_153_);
lean_dec(v_index_262_);
v___x_265_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_265_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
lean_ctor_set(v___x_265_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_265_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_265_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_265_, 5, v_funDeclsImpure_244_);
return v___x_265_;
}
case 1:
{
lean_object* v_index_266_; 
v_index_266_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_index_266_);
lean_dec_ref_known(v___x_261_, 1);
v___y_250_ = v___y_260_;
v_i_251_ = v_index_266_;
goto v___jp_249_;
}
default: 
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_260_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_index_269_; 
v_index_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_index_269_);
lean_dec_ref_known(v___x_268_, 1);
v___y_250_ = v___y_260_;
v_i_251_ = v_index_269_;
goto v___jp_249_;
}
else
{
lean_object* v___x_270_; 
lean_dec(v_fvarId_248_);
lean_del_object(v___x_246_);
lean_dec_ref(v_param_153_);
v___x_270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_270_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_270_, 1, v___y_260_);
lean_ctor_set(v___x_270_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_270_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_270_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_270_, 5, v_funDeclsImpure_244_);
return v___x_270_;
}
}
}
}
v___jp_271_:
{
lean_object* v_size_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_size_274_ = lean_ctor_get(v___y_272_, 0);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_size_274_, v___x_275_);
v___x_277_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_272_, v___x_276_, v_i_273_, v_fvarId_248_, v_param_153_);
lean_dec(v_i_273_);
v___x_278_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_278_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
lean_ctor_set(v___x_278_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_278_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_278_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_278_, 5, v_funDeclsImpure_244_);
return v___x_278_;
}
v___jp_279_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_paramsImpure_240_);
lean_dec_ref(v_paramsImpure_240_);
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___x_280_, v_fvarId_248_);
switch(lean_obj_tag(v___x_281_))
{
case 0:
{
lean_object* v_index_282_; lean_object* v_size_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_index_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_index_282_);
lean_dec_ref_known(v___x_281_, 3);
v_size_283_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_size_283_);
v___x_284_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_280_, v_size_283_, v_index_282_, v_fvarId_248_, v_param_153_);
lean_dec(v_index_282_);
v___x_285_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_285_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_ctor_set(v___x_285_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_285_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_285_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_285_, 5, v_funDeclsImpure_244_);
return v___x_285_;
}
case 1:
{
lean_object* v_index_286_; 
v_index_286_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_index_286_);
lean_dec_ref_known(v___x_281_, 1);
v___y_272_ = v___x_280_;
v_i_273_ = v_index_286_;
goto v___jp_271_;
}
default: 
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_280_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_index_289_; 
v_index_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_index_289_);
lean_dec_ref_known(v___x_288_, 1);
v___y_272_ = v___x_280_;
v_i_273_ = v_index_289_;
goto v___jp_271_;
}
else
{
lean_object* v___x_290_; 
lean_dec(v_fvarId_248_);
lean_dec_ref(v_param_153_);
v___x_290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_290_, 0, v_paramsPure_239_);
lean_ctor_set(v___x_290_, 1, v___x_280_);
lean_ctor_set(v___x_290_, 2, v_letDeclsPure_241_);
lean_ctor_set(v___x_290_, 3, v_letDeclsImpure_242_);
lean_ctor_set(v___x_290_, 4, v_funDeclsPure_243_);
lean_ctor_set(v___x_290_, 5, v_funDeclsImpure_244_);
return v___x_290_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addParam___boxed(lean_object* v_pu_324_, lean_object* v_lctx_325_, lean_object* v_param_326_){
_start:
{
uint8_t v_pu_boxed_327_; lean_object* v_res_328_; 
v_pu_boxed_327_ = lean_unbox(v_pu_324_);
v_res_328_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_boxed_327_, v_lctx_325_, v_param_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object* v_00_u03b2_329_, lean_object* v_m_330_, lean_object* v_query_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_330_, v_query_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___boxed(lean_object* v_00_u03b2_333_, lean_object* v_m_334_, lean_object* v_query_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(v_00_u03b2_333_, v_m_334_, v_query_335_);
lean_dec(v_query_335_);
lean_dec_ref(v_m_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object* v_00_u03b2_337_, lean_object* v_m_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_m_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___boxed(lean_object* v_00_u03b2_340_, lean_object* v_m_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1(v_00_u03b2_340_, v_m_341_);
lean_dec_ref(v_m_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(lean_object* v_00_u03b2_343_, lean_object* v_m_344_, lean_object* v_query_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_m_344_, v_query_345_, v_x_346_, v_x_347_, v_x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_351_, lean_object* v_m_352_, lean_object* v_query_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(v_00_u03b2_351_, v_m_352_, v_query_353_, v_x_354_, v_x_355_, v_x_356_, v_x_357_);
lean_dec(v_query_353_);
lean_dec_ref(v_m_352_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2(lean_object* v_00_u03b2_359_, lean_object* v_init_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___redArg(v_init_360_, v_b_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2___boxed(lean_object* v_00_u03b2_363_, lean_object* v_init_364_, lean_object* v_b_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2(v_00_u03b2_363_, v_init_364_, v_b_365_);
lean_dec_ref(v_b_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_367_, lean_object* v_b_368_, lean_object* v_acc_369_, lean_object* v_i_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___redArg(v_b_368_, v_acc_369_, v_i_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_372_, lean_object* v_b_373_, lean_object* v_acc_374_, lean_object* v_i_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1_spec__2_spec__3(v_00_u03b2_372_, v_b_373_, v_acc_374_, v_i_375_);
lean_dec_ref(v_b_373_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t v_pu_377_, lean_object* v_lctx_378_, lean_object* v_letDecl_379_){
_start:
{
if (v_pu_377_ == 0)
{
lean_object* v_paramsPure_380_; lean_object* v_paramsImpure_381_; lean_object* v_letDeclsPure_382_; lean_object* v_letDeclsImpure_383_; lean_object* v_funDeclsPure_384_; lean_object* v_funDeclsImpure_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_464_; 
v_paramsPure_380_ = lean_ctor_get(v_lctx_378_, 0);
v_paramsImpure_381_ = lean_ctor_get(v_lctx_378_, 1);
v_letDeclsPure_382_ = lean_ctor_get(v_lctx_378_, 2);
v_letDeclsImpure_383_ = lean_ctor_get(v_lctx_378_, 3);
v_funDeclsPure_384_ = lean_ctor_get(v_lctx_378_, 4);
v_funDeclsImpure_385_ = lean_ctor_get(v_lctx_378_, 5);
v_isSharedCheck_464_ = !lean_is_exclusive(v_lctx_378_);
if (v_isSharedCheck_464_ == 0)
{
v___x_387_ = v_lctx_378_;
v_isShared_388_ = v_isSharedCheck_464_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_funDeclsImpure_385_);
lean_inc(v_funDeclsPure_384_);
lean_inc(v_letDeclsImpure_383_);
lean_inc(v_letDeclsPure_382_);
lean_inc(v_paramsImpure_381_);
lean_inc(v_paramsPure_380_);
lean_dec(v_lctx_378_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_464_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_fvarId_389_; lean_object* v___y_391_; lean_object* v_i_392_; lean_object* v___y_401_; lean_object* v___y_413_; lean_object* v_i_414_; lean_object* v___x_432_; 
v_fvarId_389_ = lean_ctor_get(v_letDecl_379_, 0);
lean_inc(v_fvarId_389_);
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsPure_382_, v_fvarId_389_);
switch(lean_obj_tag(v___x_432_))
{
case 0:
{
lean_object* v_index_433_; lean_object* v_size_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_del_object(v___x_387_);
v_index_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_index_433_);
lean_dec_ref_known(v___x_432_, 3);
v_size_434_ = lean_ctor_get(v_letDeclsPure_382_, 0);
lean_inc(v_size_434_);
v___x_435_ = l_Std_DHashMap_Raw_setEntry___redArg(v_letDeclsPure_382_, v_size_434_, v_index_433_, v_fvarId_389_, v_letDecl_379_);
lean_dec(v_index_433_);
v___x_436_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_436_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_436_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_436_, 2, v___x_435_);
lean_ctor_set(v___x_436_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_436_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_436_, 5, v_funDeclsImpure_385_);
return v___x_436_;
}
case 1:
{
lean_object* v_index_437_; lean_object* v_size_438_; lean_object* v_keyArray_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
lean_del_object(v___x_387_);
v_index_437_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_index_437_);
lean_dec_ref_known(v___x_432_, 1);
v_size_438_ = lean_ctor_get(v_letDeclsPure_382_, 0);
v_keyArray_439_ = lean_ctor_get(v_letDeclsPure_382_, 1);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_size_438_, v___x_440_);
v___x_442_ = lean_array_get_size(v_keyArray_439_);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec(v___x_441_);
lean_dec(v_index_437_);
goto v___jp_420_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_mul(v___x_441_, v___x_444_);
v___x_446_ = lean_unsigned_to_nat(3u);
v___x_447_ = lean_nat_mul(v___x_442_, v___x_446_);
v___x_448_ = lean_nat_dec_le(v___x_445_, v___x_447_);
lean_dec(v___x_447_);
lean_dec(v___x_445_);
if (v___x_448_ == 0)
{
lean_dec(v___x_441_);
lean_dec(v_index_437_);
goto v___jp_420_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = l_Std_DHashMap_Raw_setEntry___redArg(v_letDeclsPure_382_, v___x_441_, v_index_437_, v_fvarId_389_, v_letDecl_379_);
lean_dec(v_index_437_);
v___x_450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_450_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_450_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
lean_ctor_set(v___x_450_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_450_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_450_, 5, v_funDeclsImpure_385_);
return v___x_450_;
}
}
}
default: 
{
lean_object* v_size_451_; lean_object* v_keyArray_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_size_451_ = lean_ctor_get(v_letDeclsPure_382_, 0);
v_keyArray_452_ = lean_ctor_get(v_letDeclsPure_382_, 1);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_size_451_, v___x_453_);
v___x_455_ = lean_array_get_size(v_keyArray_452_);
v___x_456_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v___x_454_);
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_letDeclsPure_382_);
lean_dec_ref(v_letDeclsPure_382_);
v___y_401_ = v___x_457_;
goto v___jp_400_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_458_ = lean_unsigned_to_nat(4u);
v___x_459_ = lean_nat_mul(v___x_454_, v___x_458_);
lean_dec(v___x_454_);
v___x_460_ = lean_unsigned_to_nat(3u);
v___x_461_ = lean_nat_mul(v___x_455_, v___x_460_);
v___x_462_ = lean_nat_dec_le(v___x_459_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v___x_459_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_letDeclsPure_382_);
lean_dec_ref(v_letDeclsPure_382_);
v___y_401_ = v___x_463_;
goto v___jp_400_;
}
else
{
v___y_401_ = v_letDeclsPure_382_;
goto v___jp_400_;
}
}
}
}
v___jp_390_:
{
lean_object* v_size_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v_size_393_ = lean_ctor_get(v___y_391_, 0);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_size_393_, v___x_394_);
v___x_396_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_391_, v___x_395_, v_i_392_, v_fvarId_389_, v_letDecl_379_);
lean_dec(v_i_392_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 2, v___x_396_);
v___x_398_ = v___x_387_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_paramsPure_380_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_paramsImpure_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_funDeclsPure_384_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v_funDeclsImpure_385_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
v___jp_400_:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___y_401_, v_fvarId_389_);
switch(lean_obj_tag(v___x_402_))
{
case 0:
{
lean_object* v_index_403_; lean_object* v_size_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_del_object(v___x_387_);
v_index_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_index_403_);
lean_dec_ref_known(v___x_402_, 3);
v_size_404_ = lean_ctor_get(v___y_401_, 0);
lean_inc(v_size_404_);
v___x_405_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_401_, v_size_404_, v_index_403_, v_fvarId_389_, v_letDecl_379_);
lean_dec(v_index_403_);
v___x_406_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_406_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_406_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
lean_ctor_set(v___x_406_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_406_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_406_, 5, v_funDeclsImpure_385_);
return v___x_406_;
}
case 1:
{
lean_object* v_index_407_; 
v_index_407_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_index_407_);
lean_dec_ref_known(v___x_402_, 1);
v___y_391_ = v___y_401_;
v_i_392_ = v_index_407_;
goto v___jp_390_;
}
default: 
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_401_, v___x_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_index_410_; 
v_index_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_index_410_);
lean_dec_ref_known(v___x_409_, 1);
v___y_391_ = v___y_401_;
v_i_392_ = v_index_410_;
goto v___jp_390_;
}
else
{
lean_object* v___x_411_; 
lean_dec(v_fvarId_389_);
lean_del_object(v___x_387_);
lean_dec_ref(v_letDecl_379_);
v___x_411_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_411_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_411_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_411_, 2, v___y_401_);
lean_ctor_set(v___x_411_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_411_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_411_, 5, v_funDeclsImpure_385_);
return v___x_411_;
}
}
}
}
v___jp_412_:
{
lean_object* v_size_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_size_415_ = lean_ctor_get(v___y_413_, 0);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v_size_415_, v___x_416_);
v___x_418_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_413_, v___x_417_, v_i_414_, v_fvarId_389_, v_letDecl_379_);
lean_dec(v_i_414_);
v___x_419_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_419_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_419_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_419_, 2, v___x_418_);
lean_ctor_set(v___x_419_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_419_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_419_, 5, v_funDeclsImpure_385_);
return v___x_419_;
}
v___jp_420_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_letDeclsPure_382_);
lean_dec_ref(v_letDeclsPure_382_);
v___x_422_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___x_421_, v_fvarId_389_);
switch(lean_obj_tag(v___x_422_))
{
case 0:
{
lean_object* v_index_423_; lean_object* v_size_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_index_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_index_423_);
lean_dec_ref_known(v___x_422_, 3);
v_size_424_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_size_424_);
v___x_425_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_421_, v_size_424_, v_index_423_, v_fvarId_389_, v_letDecl_379_);
lean_dec(v_index_423_);
v___x_426_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_426_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_426_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_426_, 2, v___x_425_);
lean_ctor_set(v___x_426_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_426_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_426_, 5, v_funDeclsImpure_385_);
return v___x_426_;
}
case 1:
{
lean_object* v_index_427_; 
v_index_427_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_index_427_);
lean_dec_ref_known(v___x_422_, 1);
v___y_413_ = v___x_421_;
v_i_414_ = v_index_427_;
goto v___jp_412_;
}
default: 
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_421_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_index_430_; 
v_index_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_index_430_);
lean_dec_ref_known(v___x_429_, 1);
v___y_413_ = v___x_421_;
v_i_414_ = v_index_430_;
goto v___jp_412_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v_fvarId_389_);
lean_dec_ref(v_letDecl_379_);
v___x_431_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_431_, 0, v_paramsPure_380_);
lean_ctor_set(v___x_431_, 1, v_paramsImpure_381_);
lean_ctor_set(v___x_431_, 2, v___x_421_);
lean_ctor_set(v___x_431_, 3, v_letDeclsImpure_383_);
lean_ctor_set(v___x_431_, 4, v_funDeclsPure_384_);
lean_ctor_set(v___x_431_, 5, v_funDeclsImpure_385_);
return v___x_431_;
}
}
}
}
}
}
else
{
lean_object* v_paramsPure_465_; lean_object* v_paramsImpure_466_; lean_object* v_letDeclsPure_467_; lean_object* v_letDeclsImpure_468_; lean_object* v_funDeclsPure_469_; lean_object* v_funDeclsImpure_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_549_; 
v_paramsPure_465_ = lean_ctor_get(v_lctx_378_, 0);
v_paramsImpure_466_ = lean_ctor_get(v_lctx_378_, 1);
v_letDeclsPure_467_ = lean_ctor_get(v_lctx_378_, 2);
v_letDeclsImpure_468_ = lean_ctor_get(v_lctx_378_, 3);
v_funDeclsPure_469_ = lean_ctor_get(v_lctx_378_, 4);
v_funDeclsImpure_470_ = lean_ctor_get(v_lctx_378_, 5);
v_isSharedCheck_549_ = !lean_is_exclusive(v_lctx_378_);
if (v_isSharedCheck_549_ == 0)
{
v___x_472_ = v_lctx_378_;
v_isShared_473_ = v_isSharedCheck_549_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_funDeclsImpure_470_);
lean_inc(v_funDeclsPure_469_);
lean_inc(v_letDeclsImpure_468_);
lean_inc(v_letDeclsPure_467_);
lean_inc(v_paramsImpure_466_);
lean_inc(v_paramsPure_465_);
lean_dec(v_lctx_378_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_549_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_fvarId_474_; lean_object* v___y_476_; lean_object* v_i_477_; lean_object* v___y_486_; lean_object* v___y_498_; lean_object* v_i_499_; lean_object* v___x_517_; 
v_fvarId_474_ = lean_ctor_get(v_letDecl_379_, 0);
lean_inc(v_fvarId_474_);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsImpure_468_, v_fvarId_474_);
switch(lean_obj_tag(v___x_517_))
{
case 0:
{
lean_object* v_index_518_; lean_object* v_size_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_del_object(v___x_472_);
v_index_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_index_518_);
lean_dec_ref_known(v___x_517_, 3);
v_size_519_ = lean_ctor_get(v_letDeclsImpure_468_, 0);
lean_inc(v_size_519_);
v___x_520_ = l_Std_DHashMap_Raw_setEntry___redArg(v_letDeclsImpure_468_, v_size_519_, v_index_518_, v_fvarId_474_, v_letDecl_379_);
lean_dec(v_index_518_);
v___x_521_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_521_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_521_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_521_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_521_, 3, v___x_520_);
lean_ctor_set(v___x_521_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_521_, 5, v_funDeclsImpure_470_);
return v___x_521_;
}
case 1:
{
lean_object* v_index_522_; lean_object* v_size_523_; lean_object* v_keyArray_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
lean_del_object(v___x_472_);
v_index_522_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_index_522_);
lean_dec_ref_known(v___x_517_, 1);
v_size_523_ = lean_ctor_get(v_letDeclsImpure_468_, 0);
v_keyArray_524_ = lean_ctor_get(v_letDeclsImpure_468_, 1);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_size_523_, v___x_525_);
v___x_527_ = lean_array_get_size(v_keyArray_524_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v___x_526_);
lean_dec(v_index_522_);
goto v___jp_505_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_529_ = lean_unsigned_to_nat(4u);
v___x_530_ = lean_nat_mul(v___x_526_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = lean_nat_mul(v___x_527_, v___x_531_);
v___x_533_ = lean_nat_dec_le(v___x_530_, v___x_532_);
lean_dec(v___x_532_);
lean_dec(v___x_530_);
if (v___x_533_ == 0)
{
lean_dec(v___x_526_);
lean_dec(v_index_522_);
goto v___jp_505_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_Std_DHashMap_Raw_setEntry___redArg(v_letDeclsImpure_468_, v___x_526_, v_index_522_, v_fvarId_474_, v_letDecl_379_);
lean_dec(v_index_522_);
v___x_535_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_535_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_535_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_535_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_535_, 3, v___x_534_);
lean_ctor_set(v___x_535_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_535_, 5, v_funDeclsImpure_470_);
return v___x_535_;
}
}
}
default: 
{
lean_object* v_size_536_; lean_object* v_keyArray_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_size_536_ = lean_ctor_get(v_letDeclsImpure_468_, 0);
v_keyArray_537_ = lean_ctor_get(v_letDeclsImpure_468_, 1);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_size_536_, v___x_538_);
v___x_540_ = lean_array_get_size(v_keyArray_537_);
v___x_541_ = lean_nat_dec_lt(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_dec(v___x_539_);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_letDeclsImpure_468_);
lean_dec_ref(v_letDeclsImpure_468_);
v___y_486_ = v___x_542_;
goto v___jp_485_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_543_ = lean_unsigned_to_nat(4u);
v___x_544_ = lean_nat_mul(v___x_539_, v___x_543_);
lean_dec(v___x_539_);
v___x_545_ = lean_unsigned_to_nat(3u);
v___x_546_ = lean_nat_mul(v___x_540_, v___x_545_);
v___x_547_ = lean_nat_dec_le(v___x_544_, v___x_546_);
lean_dec(v___x_546_);
lean_dec(v___x_544_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_letDeclsImpure_468_);
lean_dec_ref(v_letDeclsImpure_468_);
v___y_486_ = v___x_548_;
goto v___jp_485_;
}
else
{
v___y_486_ = v_letDeclsImpure_468_;
goto v___jp_485_;
}
}
}
}
v___jp_475_:
{
lean_object* v_size_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v_size_478_ = lean_ctor_get(v___y_476_, 0);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_size_478_, v___x_479_);
v___x_481_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_476_, v___x_480_, v_i_477_, v_fvarId_474_, v_letDecl_379_);
lean_dec(v_i_477_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 3, v___x_481_);
v___x_483_ = v___x_472_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_paramsPure_465_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_paramsImpure_466_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_letDeclsPure_467_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_funDeclsPure_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v_funDeclsImpure_470_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
v___jp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___y_486_, v_fvarId_474_);
switch(lean_obj_tag(v___x_487_))
{
case 0:
{
lean_object* v_index_488_; lean_object* v_size_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_del_object(v___x_472_);
v_index_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_index_488_);
lean_dec_ref_known(v___x_487_, 3);
v_size_489_ = lean_ctor_get(v___y_486_, 0);
lean_inc(v_size_489_);
v___x_490_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_486_, v_size_489_, v_index_488_, v_fvarId_474_, v_letDecl_379_);
lean_dec(v_index_488_);
v___x_491_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_491_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_491_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_491_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_491_, 3, v___x_490_);
lean_ctor_set(v___x_491_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_491_, 5, v_funDeclsImpure_470_);
return v___x_491_;
}
case 1:
{
lean_object* v_index_492_; 
v_index_492_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_index_492_);
lean_dec_ref_known(v___x_487_, 1);
v___y_476_ = v___y_486_;
v_i_477_ = v_index_492_;
goto v___jp_475_;
}
default: 
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_486_, v___x_493_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_index_495_; 
v_index_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_index_495_);
lean_dec_ref_known(v___x_494_, 1);
v___y_476_ = v___y_486_;
v_i_477_ = v_index_495_;
goto v___jp_475_;
}
else
{
lean_object* v___x_496_; 
lean_dec(v_fvarId_474_);
lean_del_object(v___x_472_);
lean_dec_ref(v_letDecl_379_);
v___x_496_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_496_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_496_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_496_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_496_, 3, v___y_486_);
lean_ctor_set(v___x_496_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_496_, 5, v_funDeclsImpure_470_);
return v___x_496_;
}
}
}
}
v___jp_497_:
{
lean_object* v_size_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_size_500_ = lean_ctor_get(v___y_498_, 0);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_size_500_, v___x_501_);
v___x_503_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_498_, v___x_502_, v_i_499_, v_fvarId_474_, v_letDecl_379_);
lean_dec(v_i_499_);
v___x_504_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_504_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_504_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_504_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_504_, 3, v___x_503_);
lean_ctor_set(v___x_504_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_504_, 5, v_funDeclsImpure_470_);
return v___x_504_;
}
v___jp_505_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_letDeclsImpure_468_);
lean_dec_ref(v_letDeclsImpure_468_);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___x_506_, v_fvarId_474_);
switch(lean_obj_tag(v___x_507_))
{
case 0:
{
lean_object* v_index_508_; lean_object* v_size_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_index_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_index_508_);
lean_dec_ref_known(v___x_507_, 3);
v_size_509_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_size_509_);
v___x_510_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_506_, v_size_509_, v_index_508_, v_fvarId_474_, v_letDecl_379_);
lean_dec(v_index_508_);
v___x_511_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_511_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_511_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_511_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_511_, 3, v___x_510_);
lean_ctor_set(v___x_511_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_511_, 5, v_funDeclsImpure_470_);
return v___x_511_;
}
case 1:
{
lean_object* v_index_512_; 
v_index_512_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_index_512_);
lean_dec_ref_known(v___x_507_, 1);
v___y_498_ = v___x_506_;
v_i_499_ = v_index_512_;
goto v___jp_497_;
}
default: 
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_506_, v___x_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_index_515_; 
v_index_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_index_515_);
lean_dec_ref_known(v___x_514_, 1);
v___y_498_ = v___x_506_;
v_i_499_ = v_index_515_;
goto v___jp_497_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_fvarId_474_);
lean_dec_ref(v_letDecl_379_);
v___x_516_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_516_, 0, v_paramsPure_465_);
lean_ctor_set(v___x_516_, 1, v_paramsImpure_466_);
lean_ctor_set(v___x_516_, 2, v_letDeclsPure_467_);
lean_ctor_set(v___x_516_, 3, v___x_506_);
lean_ctor_set(v___x_516_, 4, v_funDeclsPure_469_);
lean_ctor_set(v___x_516_, 5, v_funDeclsImpure_470_);
return v___x_516_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(lean_object* v_pu_550_, lean_object* v_lctx_551_, lean_object* v_letDecl_552_){
_start:
{
uint8_t v_pu_boxed_553_; lean_object* v_res_554_; 
v_pu_boxed_553_ = lean_unbox(v_pu_550_);
v_res_554_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_boxed_553_, v_lctx_551_, v_letDecl_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t v_pu_555_, lean_object* v_lctx_556_, lean_object* v_funDecl_557_){
_start:
{
if (v_pu_555_ == 0)
{
lean_object* v_fvarId_558_; lean_object* v_paramsPure_559_; lean_object* v_paramsImpure_560_; lean_object* v_letDeclsPure_561_; lean_object* v_letDeclsImpure_562_; lean_object* v_funDeclsPure_563_; lean_object* v_funDeclsImpure_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_642_; 
v_fvarId_558_ = lean_ctor_get(v_funDecl_557_, 0);
lean_inc(v_fvarId_558_);
v_paramsPure_559_ = lean_ctor_get(v_lctx_556_, 0);
v_paramsImpure_560_ = lean_ctor_get(v_lctx_556_, 1);
v_letDeclsPure_561_ = lean_ctor_get(v_lctx_556_, 2);
v_letDeclsImpure_562_ = lean_ctor_get(v_lctx_556_, 3);
v_funDeclsPure_563_ = lean_ctor_get(v_lctx_556_, 4);
v_funDeclsImpure_564_ = lean_ctor_get(v_lctx_556_, 5);
v_isSharedCheck_642_ = !lean_is_exclusive(v_lctx_556_);
if (v_isSharedCheck_642_ == 0)
{
v___x_566_ = v_lctx_556_;
v_isShared_567_ = v_isSharedCheck_642_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_funDeclsImpure_564_);
lean_inc(v_funDeclsPure_563_);
lean_inc(v_letDeclsImpure_562_);
lean_inc(v_letDeclsPure_561_);
lean_inc(v_paramsImpure_560_);
lean_inc(v_paramsPure_559_);
lean_dec(v_lctx_556_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_642_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___y_569_; lean_object* v_i_570_; lean_object* v___y_579_; lean_object* v___y_591_; lean_object* v_i_592_; lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsPure_563_, v_fvarId_558_);
switch(lean_obj_tag(v___x_610_))
{
case 0:
{
lean_object* v_index_611_; lean_object* v_size_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_del_object(v___x_566_);
v_index_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_index_611_);
lean_dec_ref_known(v___x_610_, 3);
v_size_612_ = lean_ctor_get(v_funDeclsPure_563_, 0);
lean_inc(v_size_612_);
v___x_613_ = l_Std_DHashMap_Raw_setEntry___redArg(v_funDeclsPure_563_, v_size_612_, v_index_611_, v_fvarId_558_, v_funDecl_557_);
lean_dec(v_index_611_);
v___x_614_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_614_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_614_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_614_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_614_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_614_, 4, v___x_613_);
lean_ctor_set(v___x_614_, 5, v_funDeclsImpure_564_);
return v___x_614_;
}
case 1:
{
lean_object* v_index_615_; lean_object* v_size_616_; lean_object* v_keyArray_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
lean_del_object(v___x_566_);
v_index_615_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_index_615_);
lean_dec_ref_known(v___x_610_, 1);
v_size_616_ = lean_ctor_get(v_funDeclsPure_563_, 0);
v_keyArray_617_ = lean_ctor_get(v_funDeclsPure_563_, 1);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_size_616_, v___x_618_);
v___x_620_ = lean_array_get_size(v_keyArray_617_);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v___x_619_);
lean_dec(v_index_615_);
goto v___jp_598_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_622_ = lean_unsigned_to_nat(4u);
v___x_623_ = lean_nat_mul(v___x_619_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(3u);
v___x_625_ = lean_nat_mul(v___x_620_, v___x_624_);
v___x_626_ = lean_nat_dec_le(v___x_623_, v___x_625_);
lean_dec(v___x_625_);
lean_dec(v___x_623_);
if (v___x_626_ == 0)
{
lean_dec(v___x_619_);
lean_dec(v_index_615_);
goto v___jp_598_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = l_Std_DHashMap_Raw_setEntry___redArg(v_funDeclsPure_563_, v___x_619_, v_index_615_, v_fvarId_558_, v_funDecl_557_);
lean_dec(v_index_615_);
v___x_628_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_628_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_628_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_628_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_628_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_628_, 4, v___x_627_);
lean_ctor_set(v___x_628_, 5, v_funDeclsImpure_564_);
return v___x_628_;
}
}
}
default: 
{
lean_object* v_size_629_; lean_object* v_keyArray_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_size_629_ = lean_ctor_get(v_funDeclsPure_563_, 0);
v_keyArray_630_ = lean_ctor_get(v_funDeclsPure_563_, 1);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_size_629_, v___x_631_);
v___x_633_ = lean_array_get_size(v_keyArray_630_);
v___x_634_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v___x_632_);
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_funDeclsPure_563_);
lean_dec_ref(v_funDeclsPure_563_);
v___y_579_ = v___x_635_;
goto v___jp_578_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_636_ = lean_unsigned_to_nat(4u);
v___x_637_ = lean_nat_mul(v___x_632_, v___x_636_);
lean_dec(v___x_632_);
v___x_638_ = lean_unsigned_to_nat(3u);
v___x_639_ = lean_nat_mul(v___x_633_, v___x_638_);
v___x_640_ = lean_nat_dec_le(v___x_637_, v___x_639_);
lean_dec(v___x_639_);
lean_dec(v___x_637_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_funDeclsPure_563_);
lean_dec_ref(v_funDeclsPure_563_);
v___y_579_ = v___x_641_;
goto v___jp_578_;
}
else
{
v___y_579_ = v_funDeclsPure_563_;
goto v___jp_578_;
}
}
}
}
v___jp_568_:
{
lean_object* v_size_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v_size_571_ = lean_ctor_get(v___y_569_, 0);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_size_571_, v___x_572_);
v___x_574_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_569_, v___x_573_, v_i_570_, v_fvarId_558_, v_funDecl_557_);
lean_dec(v_i_570_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 4, v___x_574_);
v___x_576_ = v___x_566_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_paramsPure_559_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_paramsImpure_560_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_letDeclsPure_561_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 5, v_funDeclsImpure_564_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
v___jp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___y_579_, v_fvarId_558_);
switch(lean_obj_tag(v___x_580_))
{
case 0:
{
lean_object* v_index_581_; lean_object* v_size_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_del_object(v___x_566_);
v_index_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_index_581_);
lean_dec_ref_known(v___x_580_, 3);
v_size_582_ = lean_ctor_get(v___y_579_, 0);
lean_inc(v_size_582_);
v___x_583_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_579_, v_size_582_, v_index_581_, v_fvarId_558_, v_funDecl_557_);
lean_dec(v_index_581_);
v___x_584_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_584_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_584_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_584_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_584_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_584_, 4, v___x_583_);
lean_ctor_set(v___x_584_, 5, v_funDeclsImpure_564_);
return v___x_584_;
}
case 1:
{
lean_object* v_index_585_; 
v_index_585_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_index_585_);
lean_dec_ref_known(v___x_580_, 1);
v___y_569_ = v___y_579_;
v_i_570_ = v_index_585_;
goto v___jp_568_;
}
default: 
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_579_, v___x_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_index_588_; 
v_index_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_index_588_);
lean_dec_ref_known(v___x_587_, 1);
v___y_569_ = v___y_579_;
v_i_570_ = v_index_588_;
goto v___jp_568_;
}
else
{
lean_object* v___x_589_; 
lean_del_object(v___x_566_);
lean_dec(v_fvarId_558_);
lean_dec_ref(v_funDecl_557_);
v___x_589_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_589_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_589_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_589_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_589_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_589_, 4, v___y_579_);
lean_ctor_set(v___x_589_, 5, v_funDeclsImpure_564_);
return v___x_589_;
}
}
}
}
v___jp_590_:
{
lean_object* v_size_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_size_593_ = lean_ctor_get(v___y_591_, 0);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_size_593_, v___x_594_);
v___x_596_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_591_, v___x_595_, v_i_592_, v_fvarId_558_, v_funDecl_557_);
lean_dec(v_i_592_);
v___x_597_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_597_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_597_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_597_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_597_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_597_, 4, v___x_596_);
lean_ctor_set(v___x_597_, 5, v_funDeclsImpure_564_);
return v___x_597_;
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_funDeclsPure_563_);
lean_dec_ref(v_funDeclsPure_563_);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___x_599_, v_fvarId_558_);
switch(lean_obj_tag(v___x_600_))
{
case 0:
{
lean_object* v_index_601_; lean_object* v_size_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 3);
v_size_602_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_size_602_);
v___x_603_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_599_, v_size_602_, v_index_601_, v_fvarId_558_, v_funDecl_557_);
lean_dec(v_index_601_);
v___x_604_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_604_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_604_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_604_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_604_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_604_, 4, v___x_603_);
lean_ctor_set(v___x_604_, 5, v_funDeclsImpure_564_);
return v___x_604_;
}
case 1:
{
lean_object* v_index_605_; 
v_index_605_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_605_);
lean_dec_ref_known(v___x_600_, 1);
v___y_591_ = v___x_599_;
v_i_592_ = v_index_605_;
goto v___jp_590_;
}
default: 
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_599_, v___x_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_index_608_; 
v_index_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_index_608_);
lean_dec_ref_known(v___x_607_, 1);
v___y_591_ = v___x_599_;
v_i_592_ = v_index_608_;
goto v___jp_590_;
}
else
{
lean_object* v___x_609_; 
lean_dec(v_fvarId_558_);
lean_dec_ref(v_funDecl_557_);
v___x_609_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_609_, 0, v_paramsPure_559_);
lean_ctor_set(v___x_609_, 1, v_paramsImpure_560_);
lean_ctor_set(v___x_609_, 2, v_letDeclsPure_561_);
lean_ctor_set(v___x_609_, 3, v_letDeclsImpure_562_);
lean_ctor_set(v___x_609_, 4, v___x_599_);
lean_ctor_set(v___x_609_, 5, v_funDeclsImpure_564_);
return v___x_609_;
}
}
}
}
}
}
else
{
lean_object* v_fvarId_643_; lean_object* v_paramsPure_644_; lean_object* v_paramsImpure_645_; lean_object* v_letDeclsPure_646_; lean_object* v_letDeclsImpure_647_; lean_object* v_funDeclsPure_648_; lean_object* v_funDeclsImpure_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_727_; 
v_fvarId_643_ = lean_ctor_get(v_funDecl_557_, 0);
lean_inc(v_fvarId_643_);
v_paramsPure_644_ = lean_ctor_get(v_lctx_556_, 0);
v_paramsImpure_645_ = lean_ctor_get(v_lctx_556_, 1);
v_letDeclsPure_646_ = lean_ctor_get(v_lctx_556_, 2);
v_letDeclsImpure_647_ = lean_ctor_get(v_lctx_556_, 3);
v_funDeclsPure_648_ = lean_ctor_get(v_lctx_556_, 4);
v_funDeclsImpure_649_ = lean_ctor_get(v_lctx_556_, 5);
v_isSharedCheck_727_ = !lean_is_exclusive(v_lctx_556_);
if (v_isSharedCheck_727_ == 0)
{
v___x_651_ = v_lctx_556_;
v_isShared_652_ = v_isSharedCheck_727_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_funDeclsImpure_649_);
lean_inc(v_funDeclsPure_648_);
lean_inc(v_letDeclsImpure_647_);
lean_inc(v_letDeclsPure_646_);
lean_inc(v_paramsImpure_645_);
lean_inc(v_paramsPure_644_);
lean_dec(v_lctx_556_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_727_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___y_654_; lean_object* v_i_655_; lean_object* v___y_664_; lean_object* v___y_676_; lean_object* v_i_677_; lean_object* v___x_695_; 
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsImpure_649_, v_fvarId_643_);
switch(lean_obj_tag(v___x_695_))
{
case 0:
{
lean_object* v_index_696_; lean_object* v_size_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_del_object(v___x_651_);
v_index_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_696_);
lean_dec_ref_known(v___x_695_, 3);
v_size_697_ = lean_ctor_get(v_funDeclsImpure_649_, 0);
lean_inc(v_size_697_);
v___x_698_ = l_Std_DHashMap_Raw_setEntry___redArg(v_funDeclsImpure_649_, v_size_697_, v_index_696_, v_fvarId_643_, v_funDecl_557_);
lean_dec(v_index_696_);
v___x_699_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_699_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_699_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_699_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_699_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_699_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_699_, 5, v___x_698_);
return v___x_699_;
}
case 1:
{
lean_object* v_index_700_; lean_object* v_size_701_; lean_object* v_keyArray_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
lean_del_object(v___x_651_);
v_index_700_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_700_);
lean_dec_ref_known(v___x_695_, 1);
v_size_701_ = lean_ctor_get(v_funDeclsImpure_649_, 0);
v_keyArray_702_ = lean_ctor_get(v_funDeclsImpure_649_, 1);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_size_701_, v___x_703_);
v___x_705_ = lean_array_get_size(v_keyArray_702_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec(v___x_704_);
lean_dec(v_index_700_);
goto v___jp_683_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_707_ = lean_unsigned_to_nat(4u);
v___x_708_ = lean_nat_mul(v___x_704_, v___x_707_);
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_nat_mul(v___x_705_, v___x_709_);
v___x_711_ = lean_nat_dec_le(v___x_708_, v___x_710_);
lean_dec(v___x_710_);
lean_dec(v___x_708_);
if (v___x_711_ == 0)
{
lean_dec(v___x_704_);
lean_dec(v_index_700_);
goto v___jp_683_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Std_DHashMap_Raw_setEntry___redArg(v_funDeclsImpure_649_, v___x_704_, v_index_700_, v_fvarId_643_, v_funDecl_557_);
lean_dec(v_index_700_);
v___x_713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_713_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_713_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_713_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_713_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_713_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_713_, 5, v___x_712_);
return v___x_713_;
}
}
}
default: 
{
lean_object* v_size_714_; lean_object* v_keyArray_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_size_714_ = lean_ctor_get(v_funDeclsImpure_649_, 0);
v_keyArray_715_ = lean_ctor_get(v_funDeclsImpure_649_, 1);
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_717_ = lean_nat_add(v_size_714_, v___x_716_);
v___x_718_ = lean_array_get_size(v_keyArray_715_);
v___x_719_ = lean_nat_dec_lt(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v___x_717_);
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_funDeclsImpure_649_);
lean_dec_ref(v_funDeclsImpure_649_);
v___y_664_ = v___x_720_;
goto v___jp_663_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_mul(v___x_717_, v___x_721_);
lean_dec(v___x_717_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = lean_nat_mul(v___x_718_, v___x_723_);
v___x_725_ = lean_nat_dec_le(v___x_722_, v___x_724_);
lean_dec(v___x_724_);
lean_dec(v___x_722_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_funDeclsImpure_649_);
lean_dec_ref(v_funDeclsImpure_649_);
v___y_664_ = v___x_726_;
goto v___jp_663_;
}
else
{
v___y_664_ = v_funDeclsImpure_649_;
goto v___jp_663_;
}
}
}
}
v___jp_653_:
{
lean_object* v_size_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v_size_656_ = lean_ctor_get(v___y_654_, 0);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_size_656_, v___x_657_);
v___x_659_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_654_, v___x_658_, v_i_655_, v_fvarId_643_, v_funDecl_557_);
lean_dec(v_i_655_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 5, v___x_659_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_paramsPure_644_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_paramsImpure_645_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v_letDeclsPure_646_);
lean_ctor_set(v_reuseFailAlloc_662_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v_reuseFailAlloc_662_, 4, v_funDeclsPure_648_);
lean_ctor_set(v_reuseFailAlloc_662_, 5, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
v___jp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___y_664_, v_fvarId_643_);
switch(lean_obj_tag(v___x_665_))
{
case 0:
{
lean_object* v_index_666_; lean_object* v_size_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_651_);
v_index_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_index_666_);
lean_dec_ref_known(v___x_665_, 3);
v_size_667_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_size_667_);
v___x_668_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_664_, v_size_667_, v_index_666_, v_fvarId_643_, v_funDecl_557_);
lean_dec(v_index_666_);
v___x_669_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_669_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_669_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_669_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_669_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_669_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_669_, 5, v___x_668_);
return v___x_669_;
}
case 1:
{
lean_object* v_index_670_; 
v_index_670_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_index_670_);
lean_dec_ref_known(v___x_665_, 1);
v___y_654_ = v___y_664_;
v_i_655_ = v_index_670_;
goto v___jp_653_;
}
default: 
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_664_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_index_673_; 
v_index_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_index_673_);
lean_dec_ref_known(v___x_672_, 1);
v___y_654_ = v___y_664_;
v_i_655_ = v_index_673_;
goto v___jp_653_;
}
else
{
lean_object* v___x_674_; 
lean_del_object(v___x_651_);
lean_dec(v_fvarId_643_);
lean_dec_ref(v_funDecl_557_);
v___x_674_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_674_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_674_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_674_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_674_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_674_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_674_, 5, v___y_664_);
return v___x_674_;
}
}
}
}
v___jp_675_:
{
lean_object* v_size_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_size_678_ = lean_ctor_get(v___y_676_, 0);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_size_678_, v___x_679_);
v___x_681_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_676_, v___x_680_, v_i_677_, v_fvarId_643_, v_funDecl_557_);
lean_dec(v_i_677_);
v___x_682_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_682_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_682_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_682_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_682_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_682_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_682_, 5, v___x_681_);
return v___x_682_;
}
v___jp_683_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__1___redArg(v_funDeclsImpure_649_);
lean_dec_ref(v_funDeclsImpure_649_);
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v___x_684_, v_fvarId_643_);
switch(lean_obj_tag(v___x_685_))
{
case 0:
{
lean_object* v_index_686_; lean_object* v_size_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_index_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_index_686_);
lean_dec_ref_known(v___x_685_, 3);
v_size_687_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_size_687_);
v___x_688_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_684_, v_size_687_, v_index_686_, v_fvarId_643_, v_funDecl_557_);
lean_dec(v_index_686_);
v___x_689_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_689_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_689_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_689_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_689_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_689_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_689_, 5, v___x_688_);
return v___x_689_;
}
case 1:
{
lean_object* v_index_690_; 
v_index_690_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_index_690_);
lean_dec_ref_known(v___x_685_, 1);
v___y_676_ = v___x_684_;
v_i_677_ = v_index_690_;
goto v___jp_675_;
}
default: 
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_684_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_index_693_; 
v_index_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_index_693_);
lean_dec_ref_known(v___x_692_, 1);
v___y_676_ = v___x_684_;
v_i_677_ = v_index_693_;
goto v___jp_675_;
}
else
{
lean_object* v___x_694_; 
lean_dec(v_fvarId_643_);
lean_dec_ref(v_funDecl_557_);
v___x_694_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_694_, 0, v_paramsPure_644_);
lean_ctor_set(v___x_694_, 1, v_paramsImpure_645_);
lean_ctor_set(v___x_694_, 2, v_letDeclsPure_646_);
lean_ctor_set(v___x_694_, 3, v_letDeclsImpure_647_);
lean_ctor_set(v___x_694_, 4, v_funDeclsPure_648_);
lean_ctor_set(v___x_694_, 5, v___x_684_);
return v___x_694_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(lean_object* v_pu_728_, lean_object* v_lctx_729_, lean_object* v_funDecl_730_){
_start:
{
uint8_t v_pu_boxed_731_; lean_object* v_res_732_; 
v_pu_boxed_731_ = lean_unbox(v_pu_728_);
v_res_732_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_boxed_731_, v_lctx_729_, v_funDecl_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(lean_object* v_m_733_, lean_object* v_query_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_733_, v_query_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_index_736_; lean_object* v_key_737_; lean_object* v_value_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_index_736_ = lean_ctor_get(v___x_735_, 0);
v_key_737_ = lean_ctor_get(v___x_735_, 1);
v_value_738_ = lean_ctor_get(v___x_735_, 2);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_735_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_value_738_);
lean_inc(v_key_737_);
lean_inc(v_index_736_);
lean_dec(v___x_735_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_index_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_key_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_value_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v___x_735_);
v___x_746_ = lean_box(1);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(lean_object* v_m_747_, lean_object* v_query_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_m_747_, v_query_748_);
lean_dec(v_query_748_);
lean_dec_ref(v_m_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_m_750_, v_a_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_index_753_; lean_object* v_size_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_index_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_753_);
lean_dec_ref_known(v___x_752_, 3);
v_size_754_ = lean_ctor_get(v_m_750_, 0);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_sub(v_size_754_, v___x_755_);
v___x_757_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_750_, v___x_756_, v_index_753_);
lean_dec(v_index_753_);
return v___x_757_;
}
else
{
return v_m_750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(lean_object* v_m_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_758_, v_a_759_);
lean_dec(v_a_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam(uint8_t v_pu_761_, lean_object* v_lctx_762_, lean_object* v_param_763_){
_start:
{
if (v_pu_761_ == 0)
{
lean_object* v_paramsPure_764_; lean_object* v_paramsImpure_765_; lean_object* v_letDeclsPure_766_; lean_object* v_letDeclsImpure_767_; lean_object* v_funDeclsPure_768_; lean_object* v_funDeclsImpure_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_778_; 
v_paramsPure_764_ = lean_ctor_get(v_lctx_762_, 0);
v_paramsImpure_765_ = lean_ctor_get(v_lctx_762_, 1);
v_letDeclsPure_766_ = lean_ctor_get(v_lctx_762_, 2);
v_letDeclsImpure_767_ = lean_ctor_get(v_lctx_762_, 3);
v_funDeclsPure_768_ = lean_ctor_get(v_lctx_762_, 4);
v_funDeclsImpure_769_ = lean_ctor_get(v_lctx_762_, 5);
v_isSharedCheck_778_ = !lean_is_exclusive(v_lctx_762_);
if (v_isSharedCheck_778_ == 0)
{
v___x_771_ = v_lctx_762_;
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_funDeclsImpure_769_);
lean_inc(v_funDeclsPure_768_);
lean_inc(v_letDeclsImpure_767_);
lean_inc(v_letDeclsPure_766_);
lean_inc(v_paramsImpure_765_);
lean_inc(v_paramsPure_764_);
lean_dec(v_lctx_762_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_fvarId_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v_fvarId_773_ = lean_ctor_get(v_param_763_, 0);
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsPure_764_, v_fvarId_773_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_paramsImpure_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_letDeclsPure_766_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_letDeclsImpure_767_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_funDeclsPure_768_);
lean_ctor_set(v_reuseFailAlloc_777_, 5, v_funDeclsImpure_769_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_paramsPure_779_; lean_object* v_paramsImpure_780_; lean_object* v_letDeclsPure_781_; lean_object* v_letDeclsImpure_782_; lean_object* v_funDeclsPure_783_; lean_object* v_funDeclsImpure_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v_paramsPure_779_ = lean_ctor_get(v_lctx_762_, 0);
v_paramsImpure_780_ = lean_ctor_get(v_lctx_762_, 1);
v_letDeclsPure_781_ = lean_ctor_get(v_lctx_762_, 2);
v_letDeclsImpure_782_ = lean_ctor_get(v_lctx_762_, 3);
v_funDeclsPure_783_ = lean_ctor_get(v_lctx_762_, 4);
v_funDeclsImpure_784_ = lean_ctor_get(v_lctx_762_, 5);
v_isSharedCheck_793_ = !lean_is_exclusive(v_lctx_762_);
if (v_isSharedCheck_793_ == 0)
{
v___x_786_ = v_lctx_762_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_funDeclsImpure_784_);
lean_inc(v_funDeclsPure_783_);
lean_inc(v_letDeclsImpure_782_);
lean_inc(v_letDeclsPure_781_);
lean_inc(v_paramsImpure_780_);
lean_inc(v_paramsPure_779_);
lean_dec(v_lctx_762_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_fvarId_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v_fvarId_788_ = lean_ctor_get(v_param_763_, 0);
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsImpure_780_, v_fvarId_788_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_paramsPure_779_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_letDeclsPure_781_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v_letDeclsImpure_782_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_funDeclsPure_783_);
lean_ctor_set(v_reuseFailAlloc_792_, 5, v_funDeclsImpure_784_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(lean_object* v_pu_794_, lean_object* v_lctx_795_, lean_object* v_param_796_){
_start:
{
uint8_t v_pu_boxed_797_; lean_object* v_res_798_; 
v_pu_boxed_797_ = lean_unbox(v_pu_794_);
v_res_798_ = l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_boxed_797_, v_lctx_795_, v_param_796_);
lean_dec_ref(v_param_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(lean_object* v_00_u03b2_799_, lean_object* v_m_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_800_, v_a_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(lean_object* v_00_u03b2_803_, lean_object* v_m_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(v_00_u03b2_803_, v_m_804_, v_a_805_);
lean_dec(v_a_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(lean_object* v_00_u03b2_807_, lean_object* v_m_808_, lean_object* v_query_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_m_808_, v_query_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(lean_object* v_00_u03b2_811_, lean_object* v_m_812_, lean_object* v_query_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(v_00_u03b2_811_, v_m_812_, v_query_813_);
lean_dec(v_query_813_);
lean_dec_ref(v_m_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(lean_object* v_as_815_, size_t v_i_816_, size_t v_stop_817_, lean_object* v_b_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_eq(v_i_816_, v_stop_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v_fvarId_821_; lean_object* v___x_822_; size_t v___x_823_; size_t v___x_824_; 
v___x_820_ = lean_array_uget_borrowed(v_as_815_, v_i_816_);
v_fvarId_821_ = lean_ctor_get(v___x_820_, 0);
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_b_818_, v_fvarId_821_);
v___x_823_ = ((size_t)1ULL);
v___x_824_ = lean_usize_add(v_i_816_, v___x_823_);
v_i_816_ = v___x_824_;
v_b_818_ = v___x_822_;
goto _start;
}
else
{
return v_b_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0___boxed(lean_object* v_as_826_, lean_object* v_i_827_, lean_object* v_stop_828_, lean_object* v_b_829_){
_start:
{
size_t v_i_boxed_830_; size_t v_stop_boxed_831_; lean_object* v_res_832_; 
v_i_boxed_830_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_stop_boxed_831_ = lean_unbox_usize(v_stop_828_);
lean_dec(v_stop_828_);
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_as_826_, v_i_boxed_830_, v_stop_boxed_831_, v_b_829_);
lean_dec_ref(v_as_826_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams(uint8_t v_pu_833_, lean_object* v_lctx_834_, lean_object* v_ps_835_){
_start:
{
if (v_pu_833_ == 0)
{
lean_object* v_paramsPure_836_; lean_object* v_paramsImpure_837_; lean_object* v_letDeclsPure_838_; lean_object* v_letDeclsImpure_839_; lean_object* v_funDeclsPure_840_; lean_object* v_funDeclsImpure_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_paramsPure_836_ = lean_ctor_get(v_lctx_834_, 0);
v_paramsImpure_837_ = lean_ctor_get(v_lctx_834_, 1);
v_letDeclsPure_838_ = lean_ctor_get(v_lctx_834_, 2);
v_letDeclsImpure_839_ = lean_ctor_get(v_lctx_834_, 3);
v_funDeclsPure_840_ = lean_ctor_get(v_lctx_834_, 4);
v_funDeclsImpure_841_ = lean_ctor_get(v_lctx_834_, 5);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_array_get_size(v_ps_835_);
v___x_844_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
return v_lctx_834_;
}
else
{
uint8_t v___x_845_; 
v___x_845_ = lean_nat_dec_le(v___x_843_, v___x_843_);
if (v___x_845_ == 0)
{
if (v___x_844_ == 0)
{
return v_lctx_834_;
}
else
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_855_; 
lean_inc_ref(v_funDeclsImpure_841_);
lean_inc_ref(v_funDeclsPure_840_);
lean_inc_ref(v_letDeclsImpure_839_);
lean_inc_ref(v_letDeclsPure_838_);
lean_inc_ref(v_paramsImpure_837_);
lean_inc_ref(v_paramsPure_836_);
v_isSharedCheck_855_ = !lean_is_exclusive(v_lctx_834_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; lean_object* v_unused_861_; 
v_unused_856_ = lean_ctor_get(v_lctx_834_, 5);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_lctx_834_, 4);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_lctx_834_, 3);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_lctx_834_, 2);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_lctx_834_, 1);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v_lctx_834_, 0);
lean_dec(v_unused_861_);
v___x_847_ = v_lctx_834_;
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_lctx_834_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_849_ = ((size_t)0ULL);
v___x_850_ = lean_usize_of_nat(v___x_843_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_835_, v___x_849_, v___x_850_, v_paramsPure_836_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_paramsImpure_837_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_letDeclsPure_838_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_letDeclsImpure_839_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v_funDeclsPure_840_);
lean_ctor_set(v_reuseFailAlloc_854_, 5, v_funDeclsImpure_841_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
lean_inc_ref(v_funDeclsImpure_841_);
lean_inc_ref(v_funDeclsPure_840_);
lean_inc_ref(v_letDeclsImpure_839_);
lean_inc_ref(v_letDeclsPure_838_);
lean_inc_ref(v_paramsImpure_837_);
lean_inc_ref(v_paramsPure_836_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_lctx_834_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_872_ = lean_ctor_get(v_lctx_834_, 5);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_lctx_834_, 4);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_lctx_834_, 3);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_lctx_834_, 2);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_lctx_834_, 1);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_lctx_834_, 0);
lean_dec(v_unused_877_);
v___x_863_ = v_lctx_834_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_lctx_834_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_843_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_835_, v___x_865_, v___x_866_, v_paramsPure_836_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_867_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_paramsImpure_837_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_letDeclsPure_838_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_letDeclsImpure_839_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_funDeclsPure_840_);
lean_ctor_set(v_reuseFailAlloc_870_, 5, v_funDeclsImpure_841_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
else
{
lean_object* v_paramsPure_878_; lean_object* v_paramsImpure_879_; lean_object* v_letDeclsPure_880_; lean_object* v_letDeclsImpure_881_; lean_object* v_funDeclsPure_882_; lean_object* v_funDeclsImpure_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_paramsPure_878_ = lean_ctor_get(v_lctx_834_, 0);
v_paramsImpure_879_ = lean_ctor_get(v_lctx_834_, 1);
v_letDeclsPure_880_ = lean_ctor_get(v_lctx_834_, 2);
v_letDeclsImpure_881_ = lean_ctor_get(v_lctx_834_, 3);
v_funDeclsPure_882_ = lean_ctor_get(v_lctx_834_, 4);
v_funDeclsImpure_883_ = lean_ctor_get(v_lctx_834_, 5);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_array_get_size(v_ps_835_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
return v_lctx_834_;
}
else
{
uint8_t v___x_887_; 
v___x_887_ = lean_nat_dec_le(v___x_885_, v___x_885_);
if (v___x_887_ == 0)
{
if (v___x_886_ == 0)
{
return v_lctx_834_;
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_897_; 
lean_inc_ref(v_funDeclsImpure_883_);
lean_inc_ref(v_funDeclsPure_882_);
lean_inc_ref(v_letDeclsImpure_881_);
lean_inc_ref(v_letDeclsPure_880_);
lean_inc_ref(v_paramsImpure_879_);
lean_inc_ref(v_paramsPure_878_);
v_isSharedCheck_897_ = !lean_is_exclusive(v_lctx_834_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; lean_object* v_unused_899_; lean_object* v_unused_900_; lean_object* v_unused_901_; lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_898_ = lean_ctor_get(v_lctx_834_, 5);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_lctx_834_, 4);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_lctx_834_, 3);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_lctx_834_, 2);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_lctx_834_, 1);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_lctx_834_, 0);
lean_dec(v_unused_903_);
v___x_889_ = v_lctx_834_;
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_lctx_834_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_891_ = ((size_t)0ULL);
v___x_892_ = lean_usize_of_nat(v___x_885_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_835_, v___x_891_, v___x_892_, v_paramsImpure_879_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_893_);
v___x_895_ = v___x_889_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_paramsPure_878_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_letDeclsPure_880_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_letDeclsImpure_881_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_funDeclsPure_882_);
lean_ctor_set(v_reuseFailAlloc_896_, 5, v_funDeclsImpure_883_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
lean_inc_ref(v_funDeclsImpure_883_);
lean_inc_ref(v_funDeclsPure_882_);
lean_inc_ref(v_letDeclsImpure_881_);
lean_inc_ref(v_letDeclsPure_880_);
lean_inc_ref(v_paramsImpure_879_);
lean_inc_ref(v_paramsPure_878_);
v_isSharedCheck_913_ = !lean_is_exclusive(v_lctx_834_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; lean_object* v_unused_919_; 
v_unused_914_ = lean_ctor_get(v_lctx_834_, 5);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_lctx_834_, 4);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_lctx_834_, 3);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_lctx_834_, 2);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_lctx_834_, 1);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_lctx_834_, 0);
lean_dec(v_unused_919_);
v___x_905_ = v_lctx_834_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_dec(v_lctx_834_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_907_ = ((size_t)0ULL);
v___x_908_ = lean_usize_of_nat(v___x_885_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_835_, v___x_907_, v___x_908_, v_paramsImpure_879_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_909_);
v___x_911_ = v___x_905_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_paramsPure_878_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_letDeclsPure_880_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_letDeclsImpure_881_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_funDeclsPure_882_);
lean_ctor_set(v_reuseFailAlloc_912_, 5, v_funDeclsImpure_883_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(lean_object* v_pu_920_, lean_object* v_lctx_921_, lean_object* v_ps_922_){
_start:
{
uint8_t v_pu_boxed_923_; lean_object* v_res_924_; 
v_pu_boxed_923_ = lean_unbox(v_pu_920_);
v_res_924_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_boxed_923_, v_lctx_921_, v_ps_922_);
lean_dec_ref(v_ps_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(uint8_t v_pu_925_, lean_object* v_lctx_926_, lean_object* v_decl_927_){
_start:
{
if (v_pu_925_ == 0)
{
lean_object* v_paramsPure_928_; lean_object* v_paramsImpure_929_; lean_object* v_letDeclsPure_930_; lean_object* v_letDeclsImpure_931_; lean_object* v_funDeclsPure_932_; lean_object* v_funDeclsImpure_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_942_; 
v_paramsPure_928_ = lean_ctor_get(v_lctx_926_, 0);
v_paramsImpure_929_ = lean_ctor_get(v_lctx_926_, 1);
v_letDeclsPure_930_ = lean_ctor_get(v_lctx_926_, 2);
v_letDeclsImpure_931_ = lean_ctor_get(v_lctx_926_, 3);
v_funDeclsPure_932_ = lean_ctor_get(v_lctx_926_, 4);
v_funDeclsImpure_933_ = lean_ctor_get(v_lctx_926_, 5);
v_isSharedCheck_942_ = !lean_is_exclusive(v_lctx_926_);
if (v_isSharedCheck_942_ == 0)
{
v___x_935_ = v_lctx_926_;
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_funDeclsImpure_933_);
lean_inc(v_funDeclsPure_932_);
lean_inc(v_letDeclsImpure_931_);
lean_inc(v_letDeclsPure_930_);
lean_inc(v_paramsImpure_929_);
lean_inc(v_paramsPure_928_);
lean_dec(v_lctx_926_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_fvarId_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_fvarId_937_ = lean_ctor_get(v_decl_927_, 0);
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsPure_930_, v_fvarId_937_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 2, v___x_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_paramsPure_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_paramsImpure_929_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_letDeclsImpure_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_funDeclsPure_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v_funDeclsImpure_933_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v_paramsPure_943_; lean_object* v_paramsImpure_944_; lean_object* v_letDeclsPure_945_; lean_object* v_letDeclsImpure_946_; lean_object* v_funDeclsPure_947_; lean_object* v_funDeclsImpure_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_957_; 
v_paramsPure_943_ = lean_ctor_get(v_lctx_926_, 0);
v_paramsImpure_944_ = lean_ctor_get(v_lctx_926_, 1);
v_letDeclsPure_945_ = lean_ctor_get(v_lctx_926_, 2);
v_letDeclsImpure_946_ = lean_ctor_get(v_lctx_926_, 3);
v_funDeclsPure_947_ = lean_ctor_get(v_lctx_926_, 4);
v_funDeclsImpure_948_ = lean_ctor_get(v_lctx_926_, 5);
v_isSharedCheck_957_ = !lean_is_exclusive(v_lctx_926_);
if (v_isSharedCheck_957_ == 0)
{
v___x_950_ = v_lctx_926_;
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_funDeclsImpure_948_);
lean_inc(v_funDeclsPure_947_);
lean_inc(v_letDeclsImpure_946_);
lean_inc(v_letDeclsPure_945_);
lean_inc(v_paramsImpure_944_);
lean_inc(v_paramsPure_943_);
lean_dec(v_lctx_926_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_fvarId_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v_fvarId_952_ = lean_ctor_get(v_decl_927_, 0);
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsImpure_946_, v_fvarId_952_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 3, v___x_953_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_paramsPure_943_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_paramsImpure_944_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_letDeclsPure_945_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_funDeclsPure_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 5, v_funDeclsImpure_948_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(lean_object* v_pu_958_, lean_object* v_lctx_959_, lean_object* v_decl_960_){
_start:
{
uint8_t v_pu_boxed_961_; lean_object* v_res_962_; 
v_pu_boxed_961_ = lean_unbox(v_pu_958_);
v_res_962_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_boxed_961_, v_lctx_959_, v_decl_960_);
lean_dec_ref(v_decl_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(uint8_t v_pu_963_, lean_object* v_lctx_964_, lean_object* v_decl_965_, uint8_t v_recursive_966_){
_start:
{
lean_object* v___y_968_; 
if (v_pu_963_ == 0)
{
lean_object* v_fvarId_973_; lean_object* v_paramsPure_974_; lean_object* v_paramsImpure_975_; lean_object* v_letDeclsPure_976_; lean_object* v_letDeclsImpure_977_; lean_object* v_funDeclsPure_978_; lean_object* v_funDeclsImpure_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_fvarId_973_ = lean_ctor_get(v_decl_965_, 0);
v_paramsPure_974_ = lean_ctor_get(v_lctx_964_, 0);
v_paramsImpure_975_ = lean_ctor_get(v_lctx_964_, 1);
v_letDeclsPure_976_ = lean_ctor_get(v_lctx_964_, 2);
v_letDeclsImpure_977_ = lean_ctor_get(v_lctx_964_, 3);
v_funDeclsPure_978_ = lean_ctor_get(v_lctx_964_, 4);
v_funDeclsImpure_979_ = lean_ctor_get(v_lctx_964_, 5);
v_isSharedCheck_987_ = !lean_is_exclusive(v_lctx_964_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v_lctx_964_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_funDeclsImpure_979_);
lean_inc(v_funDeclsPure_978_);
lean_inc(v_letDeclsImpure_977_);
lean_inc(v_letDeclsPure_976_);
lean_inc(v_paramsImpure_975_);
lean_inc(v_paramsPure_974_);
lean_dec(v_lctx_964_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsPure_978_, v_fvarId_973_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 4, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_paramsPure_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_paramsImpure_975_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_letDeclsPure_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_letDeclsImpure_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_986_, 5, v_funDeclsImpure_979_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
v___y_968_ = v___x_985_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v_fvarId_988_; lean_object* v_paramsPure_989_; lean_object* v_paramsImpure_990_; lean_object* v_letDeclsPure_991_; lean_object* v_letDeclsImpure_992_; lean_object* v_funDeclsPure_993_; lean_object* v_funDeclsImpure_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_fvarId_988_ = lean_ctor_get(v_decl_965_, 0);
v_paramsPure_989_ = lean_ctor_get(v_lctx_964_, 0);
v_paramsImpure_990_ = lean_ctor_get(v_lctx_964_, 1);
v_letDeclsPure_991_ = lean_ctor_get(v_lctx_964_, 2);
v_letDeclsImpure_992_ = lean_ctor_get(v_lctx_964_, 3);
v_funDeclsPure_993_ = lean_ctor_get(v_lctx_964_, 4);
v_funDeclsImpure_994_ = lean_ctor_get(v_lctx_964_, 5);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_lctx_964_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v_lctx_964_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_funDeclsImpure_994_);
lean_inc(v_funDeclsPure_993_);
lean_inc(v_letDeclsImpure_992_);
lean_inc(v_letDeclsPure_991_);
lean_inc(v_paramsImpure_990_);
lean_inc(v_paramsPure_989_);
lean_dec(v_lctx_964_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsImpure_994_, v_fvarId_988_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 5, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_paramsPure_989_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_paramsImpure_990_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_letDeclsPure_991_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_letDeclsImpure_992_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_funDeclsPure_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v___y_968_ = v___x_1000_;
goto v___jp_967_;
}
}
}
v___jp_967_:
{
if (v_recursive_966_ == 0)
{
return v___y_968_;
}
else
{
lean_object* v_params_969_; lean_object* v_value_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_params_969_ = lean_ctor_get(v_decl_965_, 2);
v_value_970_ = lean_ctor_get(v_decl_965_, 4);
v___x_971_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_963_, v___y_968_, v_params_969_);
v___x_972_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_963_, v_value_970_, v___x_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode(uint8_t v_pu_1003_, lean_object* v_code_1004_, lean_object* v_lctx_1005_){
_start:
{
switch(lean_obj_tag(v_code_1004_))
{
case 0:
{
lean_object* v_decl_1006_; lean_object* v_k_1007_; lean_object* v___x_1008_; 
v_decl_1006_ = lean_ctor_get(v_code_1004_, 0);
v_k_1007_ = lean_ctor_get(v_code_1004_, 1);
v___x_1008_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_1003_, v_lctx_1005_, v_decl_1006_);
v_code_1004_ = v_k_1007_;
v_lctx_1005_ = v___x_1008_;
goto _start;
}
case 1:
{
lean_object* v_decl_1010_; lean_object* v_k_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; 
v_decl_1010_ = lean_ctor_get(v_code_1004_, 0);
v_k_1011_ = lean_ctor_get(v_code_1004_, 1);
v___x_1012_ = 1;
v___x_1013_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1003_, v_lctx_1005_, v_decl_1010_, v___x_1012_);
v_code_1004_ = v_k_1011_;
v_lctx_1005_ = v___x_1013_;
goto _start;
}
case 2:
{
lean_object* v_decl_1015_; lean_object* v_k_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; 
v_decl_1015_ = lean_ctor_get(v_code_1004_, 0);
v_k_1016_ = lean_ctor_get(v_code_1004_, 1);
v___x_1017_ = 1;
v___x_1018_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_1003_, v_lctx_1005_, v_decl_1015_, v___x_1017_);
v_code_1004_ = v_k_1016_;
v_lctx_1005_ = v___x_1018_;
goto _start;
}
case 4:
{
lean_object* v_cases_1020_; lean_object* v_alts_1021_; lean_object* v___x_1022_; 
v_cases_1020_ = lean_ctor_get(v_code_1004_, 0);
v_alts_1021_ = lean_ctor_get(v_cases_1020_, 3);
v___x_1022_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_1003_, v_alts_1021_, v_lctx_1005_);
return v___x_1022_;
}
case 7:
{
lean_object* v_k_1023_; 
v_k_1023_ = lean_ctor_get(v_code_1004_, 3);
v_code_1004_ = v_k_1023_;
goto _start;
}
case 8:
{
lean_object* v_k_1025_; 
v_k_1025_ = lean_ctor_get(v_code_1004_, 3);
v_code_1004_ = v_k_1025_;
goto _start;
}
case 9:
{
lean_object* v_k_1027_; 
v_k_1027_ = lean_ctor_get(v_code_1004_, 5);
v_code_1004_ = v_k_1027_;
goto _start;
}
case 10:
{
lean_object* v_k_1029_; 
v_k_1029_ = lean_ctor_get(v_code_1004_, 2);
v_code_1004_ = v_k_1029_;
goto _start;
}
case 11:
{
lean_object* v_k_1031_; 
v_k_1031_ = lean_ctor_get(v_code_1004_, 2);
v_code_1004_ = v_k_1031_;
goto _start;
}
case 12:
{
lean_object* v_k_1033_; 
v_k_1033_ = lean_ctor_get(v_code_1004_, 3);
v_code_1004_ = v_k_1033_;
goto _start;
}
case 13:
{
lean_object* v_k_1035_; 
v_k_1035_ = lean_ctor_get(v_code_1004_, 1);
v_code_1004_ = v_k_1035_;
goto _start;
}
default: 
{
return v_lctx_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(uint8_t v_pu_1037_, lean_object* v_as_1038_, size_t v_i_1039_, size_t v_stop_1040_, lean_object* v_b_1041_){
_start:
{
lean_object* v___y_1043_; uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_eq(v_i_1039_, v_stop_1040_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_array_uget_borrowed(v_as_1038_, v_i_1039_);
switch(lean_obj_tag(v___x_1048_))
{
case 0:
{
lean_object* v_params_1049_; lean_object* v_code_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_params_1049_ = lean_ctor_get(v___x_1048_, 1);
v_code_1050_ = lean_ctor_get(v___x_1048_, 2);
v___x_1051_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_1037_, v_b_1041_, v_params_1049_);
v___x_1052_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1037_, v_code_1050_, v___x_1051_);
v___y_1043_ = v___x_1052_;
goto v___jp_1042_;
}
case 1:
{
lean_object* v_code_1053_; lean_object* v___x_1054_; 
v_code_1053_ = lean_ctor_get(v___x_1048_, 1);
v___x_1054_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1037_, v_code_1053_, v_b_1041_);
v___y_1043_ = v___x_1054_;
goto v___jp_1042_;
}
default: 
{
lean_object* v_code_1055_; lean_object* v___x_1056_; 
v_code_1055_ = lean_ctor_get(v___x_1048_, 0);
v___x_1056_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1037_, v_code_1055_, v_b_1041_);
v___y_1043_ = v___x_1056_;
goto v___jp_1042_;
}
}
}
else
{
return v_b_1041_;
}
v___jp_1042_:
{
size_t v___x_1044_; size_t v___x_1045_; 
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_1039_, v___x_1044_);
v_i_1039_ = v___x_1045_;
v_b_1041_ = v___y_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts(uint8_t v_pu_1057_, lean_object* v_alts_1058_, lean_object* v_lctx_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_array_get_size(v_alts_1058_);
v___x_1062_ = lean_nat_dec_lt(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
return v_lctx_1059_;
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_nat_dec_le(v___x_1061_, v___x_1061_);
if (v___x_1063_ == 0)
{
if (v___x_1062_ == 0)
{
return v_lctx_1059_;
}
else
{
size_t v___x_1064_; size_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((size_t)0ULL);
v___x_1065_ = lean_usize_of_nat(v___x_1061_);
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_1057_, v_alts_1058_, v___x_1064_, v___x_1065_, v_lctx_1059_);
return v___x_1066_;
}
}
else
{
size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = ((size_t)0ULL);
v___x_1068_ = lean_usize_of_nat(v___x_1061_);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_1057_, v_alts_1058_, v___x_1067_, v___x_1068_, v_lctx_1059_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(lean_object* v_pu_1070_, lean_object* v_alts_1071_, lean_object* v_lctx_1072_){
_start:
{
uint8_t v_pu_boxed_1073_; lean_object* v_res_1074_; 
v_pu_boxed_1073_ = lean_unbox(v_pu_1070_);
v_res_1074_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_boxed_1073_, v_alts_1071_, v_lctx_1072_);
lean_dec_ref(v_alts_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(lean_object* v_pu_1075_, lean_object* v_as_1076_, lean_object* v_i_1077_, lean_object* v_stop_1078_, lean_object* v_b_1079_){
_start:
{
uint8_t v_pu_boxed_1080_; size_t v_i_boxed_1081_; size_t v_stop_boxed_1082_; lean_object* v_res_1083_; 
v_pu_boxed_1080_ = lean_unbox(v_pu_1075_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_stop_boxed_1082_ = lean_unbox_usize(v_stop_1078_);
lean_dec(v_stop_1078_);
v_res_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_boxed_1080_, v_as_1076_, v_i_boxed_1081_, v_stop_boxed_1082_, v_b_1079_);
lean_dec_ref(v_as_1076_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(lean_object* v_pu_1084_, lean_object* v_lctx_1085_, lean_object* v_decl_1086_, lean_object* v_recursive_1087_){
_start:
{
uint8_t v_pu_boxed_1088_; uint8_t v_recursive_boxed_1089_; lean_object* v_res_1090_; 
v_pu_boxed_1088_ = lean_unbox(v_pu_1084_);
v_recursive_boxed_1089_ = lean_unbox(v_recursive_1087_);
v_res_1090_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(v_pu_boxed_1088_, v_lctx_1085_, v_decl_1086_, v_recursive_boxed_1089_);
lean_dec_ref(v_decl_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(lean_object* v_pu_1091_, lean_object* v_code_1092_, lean_object* v_lctx_1093_){
_start:
{
uint8_t v_pu_boxed_1094_; lean_object* v_res_1095_; 
v_pu_boxed_1094_ = lean_unbox(v_pu_1091_);
v_res_1095_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_boxed_1094_, v_code_1092_, v_lctx_1093_);
lean_dec_ref(v_code_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params(lean_object* v_lctx_1096_, uint8_t v_pu_1097_){
_start:
{
if (v_pu_1097_ == 0)
{
lean_object* v_paramsPure_1098_; 
v_paramsPure_1098_ = lean_ctor_get(v_lctx_1096_, 0);
lean_inc_ref(v_paramsPure_1098_);
return v_paramsPure_1098_;
}
else
{
lean_object* v_paramsImpure_1099_; 
v_paramsImpure_1099_ = lean_ctor_get(v_lctx_1096_, 1);
lean_inc_ref(v_paramsImpure_1099_);
return v_paramsImpure_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_params___boxed(lean_object* v_lctx_1100_, lean_object* v_pu_1101_){
_start:
{
uint8_t v_pu_boxed_1102_; lean_object* v_res_1103_; 
v_pu_boxed_1102_ = lean_unbox(v_pu_1101_);
v_res_1103_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_1100_, v_pu_boxed_1102_);
lean_dec_ref(v_lctx_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls(lean_object* v_lctx_1104_, uint8_t v_pu_1105_){
_start:
{
if (v_pu_1105_ == 0)
{
lean_object* v_letDeclsPure_1106_; 
v_letDeclsPure_1106_ = lean_ctor_get(v_lctx_1104_, 2);
lean_inc_ref(v_letDeclsPure_1106_);
return v_letDeclsPure_1106_;
}
else
{
lean_object* v_letDeclsImpure_1107_; 
v_letDeclsImpure_1107_ = lean_ctor_get(v_lctx_1104_, 3);
lean_inc_ref(v_letDeclsImpure_1107_);
return v_letDeclsImpure_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(lean_object* v_lctx_1108_, lean_object* v_pu_1109_){
_start:
{
uint8_t v_pu_boxed_1110_; lean_object* v_res_1111_; 
v_pu_boxed_1110_ = lean_unbox(v_pu_1109_);
v_res_1111_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_1108_, v_pu_boxed_1110_);
lean_dec_ref(v_lctx_1108_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls(lean_object* v_lctx_1112_, uint8_t v_pu_1113_){
_start:
{
if (v_pu_1113_ == 0)
{
lean_object* v_funDeclsPure_1114_; 
v_funDeclsPure_1114_ = lean_ctor_get(v_lctx_1112_, 4);
lean_inc_ref(v_funDeclsPure_1114_);
return v_funDeclsPure_1114_;
}
else
{
lean_object* v_funDeclsImpure_1115_; 
v_funDeclsImpure_1115_ = lean_ctor_get(v_lctx_1112_, 5);
lean_inc_ref(v_funDeclsImpure_1115_);
return v_funDeclsImpure_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(lean_object* v_lctx_1116_, lean_object* v_pu_1117_){
_start:
{
uint8_t v_pu_boxed_1118_; lean_object* v_res_1119_; 
v_pu_boxed_1118_ = lean_unbox(v_pu_1117_);
v_res_1119_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_1116_, v_pu_boxed_1118_);
lean_dec_ref(v_lctx_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2_spec__4(lean_object* v_b_1120_, lean_object* v_acc_1121_, lean_object* v_i_1122_){
_start:
{
lean_object* v_keyArray_1127_; lean_object* v_valueArray_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_keyArray_1127_ = lean_ctor_get(v_b_1120_, 1);
v_valueArray_1128_ = lean_ctor_get(v_b_1120_, 2);
v___x_1129_ = lean_array_get_size(v_keyArray_1127_);
v___x_1130_ = lean_nat_dec_lt(v_i_1122_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec(v_i_1122_);
return v_acc_1121_;
}
else
{
lean_object* v___x_1131_; uint8_t v_isSome_1132_; 
v___x_1131_ = lean_array_fget_borrowed(v_keyArray_1127_, v_i_1122_);
v_isSome_1132_ = lean_noption_is_some(v___x_1131_);
if (v_isSome_1132_ == 0)
{
goto v___jp_1123_;
}
else
{
lean_object* v___x_1133_; uint8_t v_isSome_1134_; 
v___x_1133_ = lean_array_fget_borrowed(v_valueArray_1128_, v_i_1122_);
v_isSome_1134_ = lean_noption_is_some(v___x_1133_);
if (v_isSome_1134_ == 0)
{
goto v___jp_1123_;
}
else
{
lean_object* v_val_1135_; lean_object* v_fvarId_1136_; lean_object* v_binderName_1137_; lean_object* v_type_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_inc(v___x_1133_);
v_val_1135_ = lean_noption_get(v___x_1133_);
v_fvarId_1136_ = lean_ctor_get(v_val_1135_, 0);
lean_inc(v_fvarId_1136_);
v_binderName_1137_ = lean_ctor_get(v_val_1135_, 1);
lean_inc(v_binderName_1137_);
v_type_1138_ = lean_ctor_get(v_val_1135_, 3);
lean_inc_ref(v_type_1138_);
lean_dec(v_val_1135_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = 0;
v___x_1141_ = 0;
v___x_1142_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v_fvarId_1136_);
lean_ctor_set(v___x_1142_, 2, v_binderName_1137_);
lean_ctor_set(v___x_1142_, 3, v_type_1138_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*4, v___x_1140_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*4 + 1, v___x_1141_);
v___x_1143_ = l_Lean_LocalContext_addDecl(v_acc_1121_, v___x_1142_);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_add(v_i_1122_, v___x_1144_);
lean_dec(v_i_1122_);
v_acc_1121_ = v___x_1143_;
v_i_1122_ = v___x_1145_;
goto _start;
}
}
}
v___jp_1123_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_i_1122_, v___x_1124_);
lean_dec(v_i_1122_);
v_i_1122_ = v___x_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2_spec__4___boxed(lean_object* v_b_1147_, lean_object* v_acc_1148_, lean_object* v_i_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2_spec__4(v_b_1147_, v_acc_1148_, v_i_1149_);
lean_dec_ref(v_b_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(lean_object* v_init_1151_, lean_object* v_b_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2_spec__4(v_b_1152_, v_init_1151_, v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(lean_object* v_init_1155_, lean_object* v_b_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_init_1155_, v_b_1156_);
lean_dec_ref(v_b_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1_spec__2(uint8_t v_pu_1158_, lean_object* v_b_1159_, lean_object* v_acc_1160_, lean_object* v_i_1161_){
_start:
{
lean_object* v_keyArray_1166_; lean_object* v_valueArray_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_keyArray_1166_ = lean_ctor_get(v_b_1159_, 1);
v_valueArray_1167_ = lean_ctor_get(v_b_1159_, 2);
v___x_1168_ = lean_array_get_size(v_keyArray_1166_);
v___x_1169_ = lean_nat_dec_lt(v_i_1161_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_dec(v_i_1161_);
return v_acc_1160_;
}
else
{
lean_object* v___x_1170_; uint8_t v_isSome_1171_; 
v___x_1170_ = lean_array_fget_borrowed(v_keyArray_1166_, v_i_1161_);
v_isSome_1171_ = lean_noption_is_some(v___x_1170_);
if (v_isSome_1171_ == 0)
{
goto v___jp_1162_;
}
else
{
lean_object* v___x_1172_; uint8_t v_isSome_1173_; 
v___x_1172_ = lean_array_fget_borrowed(v_valueArray_1167_, v_i_1161_);
v_isSome_1173_ = lean_noption_is_some(v___x_1172_);
if (v_isSome_1173_ == 0)
{
goto v___jp_1162_;
}
else
{
lean_object* v_val_1174_; lean_object* v_fvarId_1175_; lean_object* v_binderName_1176_; lean_object* v_type_1177_; lean_object* v_value_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_inc(v___x_1172_);
v_val_1174_ = lean_noption_get(v___x_1172_);
v_fvarId_1175_ = lean_ctor_get(v_val_1174_, 0);
lean_inc(v_fvarId_1175_);
v_binderName_1176_ = lean_ctor_get(v_val_1174_, 1);
lean_inc(v_binderName_1176_);
v_type_1177_ = lean_ctor_get(v_val_1174_, 2);
lean_inc_ref(v_type_1177_);
v_value_1178_ = lean_ctor_get(v_val_1174_, 3);
lean_inc(v_value_1178_);
lean_dec(v_val_1174_);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_1158_, v_value_1178_);
v___x_1181_ = 0;
v___x_1182_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_1182_, 0, v___x_1179_);
lean_ctor_set(v___x_1182_, 1, v_fvarId_1175_);
lean_ctor_set(v___x_1182_, 2, v_binderName_1176_);
lean_ctor_set(v___x_1182_, 3, v_type_1177_);
lean_ctor_set(v___x_1182_, 4, v___x_1180_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*5, v_isSome_1173_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*5 + 1, v___x_1181_);
v___x_1183_ = l_Lean_LocalContext_addDecl(v_acc_1160_, v___x_1182_);
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_nat_add(v_i_1161_, v___x_1184_);
lean_dec(v_i_1161_);
v_acc_1160_ = v___x_1183_;
v_i_1161_ = v___x_1185_;
goto _start;
}
}
}
v___jp_1162_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1161_, v___x_1163_);
lean_dec(v_i_1161_);
v_i_1161_ = v___x_1164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1_spec__2___boxed(lean_object* v_pu_1187_, lean_object* v_b_1188_, lean_object* v_acc_1189_, lean_object* v_i_1190_){
_start:
{
uint8_t v_pu_boxed_1191_; lean_object* v_res_1192_; 
v_pu_boxed_1191_ = lean_unbox(v_pu_1187_);
v_res_1192_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1_spec__2(v_pu_boxed_1191_, v_b_1188_, v_acc_1189_, v_i_1190_);
lean_dec_ref(v_b_1188_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(uint8_t v_pu_1193_, lean_object* v_init_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1_spec__2(v_pu_1193_, v_b_1195_, v_init_1194_, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(lean_object* v_pu_1198_, lean_object* v_init_1199_, lean_object* v_b_1200_){
_start:
{
uint8_t v_pu_boxed_1201_; lean_object* v_res_1202_; 
v_pu_boxed_1201_ = lean_unbox(v_pu_1198_);
v_res_1202_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_pu_boxed_1201_, v_init_1199_, v_b_1200_);
lean_dec_ref(v_b_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_spec__0(lean_object* v_b_1203_, lean_object* v_acc_1204_, lean_object* v_i_1205_){
_start:
{
lean_object* v_keyArray_1210_; lean_object* v_valueArray_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_keyArray_1210_ = lean_ctor_get(v_b_1203_, 1);
v_valueArray_1211_ = lean_ctor_get(v_b_1203_, 2);
v___x_1212_ = lean_array_get_size(v_keyArray_1210_);
v___x_1213_ = lean_nat_dec_lt(v_i_1205_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_i_1205_);
return v_acc_1204_;
}
else
{
lean_object* v___x_1214_; uint8_t v_isSome_1215_; 
v___x_1214_ = lean_array_fget_borrowed(v_keyArray_1210_, v_i_1205_);
v_isSome_1215_ = lean_noption_is_some(v___x_1214_);
if (v_isSome_1215_ == 0)
{
goto v___jp_1206_;
}
else
{
lean_object* v___x_1216_; uint8_t v_isSome_1217_; 
v___x_1216_ = lean_array_fget_borrowed(v_valueArray_1211_, v_i_1205_);
v_isSome_1217_ = lean_noption_is_some(v___x_1216_);
if (v_isSome_1217_ == 0)
{
goto v___jp_1206_;
}
else
{
lean_object* v_val_1218_; lean_object* v_fvarId_1219_; lean_object* v_binderName_1220_; lean_object* v_type_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_inc(v___x_1216_);
v_val_1218_ = lean_noption_get(v___x_1216_);
v_fvarId_1219_ = lean_ctor_get(v_val_1218_, 0);
lean_inc(v_fvarId_1219_);
v_binderName_1220_ = lean_ctor_get(v_val_1218_, 1);
lean_inc(v_binderName_1220_);
v_type_1221_ = lean_ctor_get(v_val_1218_, 2);
lean_inc_ref(v_type_1221_);
lean_dec(v_val_1218_);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = 0;
v___x_1224_ = 0;
v___x_1225_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1225_, 0, v___x_1222_);
lean_ctor_set(v___x_1225_, 1, v_fvarId_1219_);
lean_ctor_set(v___x_1225_, 2, v_binderName_1220_);
lean_ctor_set(v___x_1225_, 3, v_type_1221_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*4, v___x_1223_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*4 + 1, v___x_1224_);
v___x_1226_ = l_Lean_LocalContext_addDecl(v_acc_1204_, v___x_1225_);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_i_1205_, v___x_1227_);
lean_dec(v_i_1205_);
v_acc_1204_ = v___x_1226_;
v_i_1205_ = v___x_1228_;
goto _start;
}
}
}
v___jp_1206_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_i_1205_, v___x_1207_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_spec__0___boxed(lean_object* v_b_1230_, lean_object* v_acc_1231_, lean_object* v_i_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_spec__0(v_b_1230_, v_acc_1231_, v_i_1232_);
lean_dec_ref(v_b_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(lean_object* v_init_1234_, lean_object* v_b_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = l_Std_DHashMap_Raw_forInFrom___at___00Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0_spec__0(v_b_1235_, v_init_1234_, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(lean_object* v_init_1238_, lean_object* v_b_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_init_1238_, v_b_1239_);
lean_dec_ref(v_b_1239_);
return v_res_1240_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0(void){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(32u);
v___x_1245_ = lean_mk_empty_array_with_capacity(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3(void){
_start:
{
size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1247_ = ((size_t)5ULL);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = lean_unsigned_to_nat(32u);
v___x_1250_ = lean_mk_empty_array_with_capacity(v___x_1249_);
v___x_1251_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2);
v___x_1252_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1250_);
lean_ctor_set(v___x_1252_, 2, v___x_1248_);
lean_ctor_set(v___x_1252_, 3, v___x_1248_);
lean_ctor_set_usize(v___x_1252_, 4, v___x_1247_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_result_1256_; 
v___x_1253_ = lean_box(1);
v___x_1254_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3);
v___x_1255_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1);
v_result_1256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_result_1256_, 0, v___x_1255_);
lean_ctor_set(v_result_1256_, 1, v___x_1254_);
lean_ctor_set(v_result_1256_, 2, v___x_1253_);
return v_result_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object* v_lctx_1257_, uint8_t v_pu_1258_){
_start:
{
lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v_result_1267_; lean_object* v___y_1269_; 
v_result_1267_ = lean_obj_once(&l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4, &l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once, _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4);
if (v_pu_1258_ == 0)
{
lean_object* v_paramsPure_1273_; 
v_paramsPure_1273_ = lean_ctor_get(v_lctx_1257_, 0);
v___y_1269_ = v_paramsPure_1273_;
goto v___jp_1268_;
}
else
{
lean_object* v_paramsImpure_1274_; 
v_paramsImpure_1274_ = lean_ctor_get(v_lctx_1257_, 1);
v___y_1269_ = v_paramsImpure_1274_;
goto v___jp_1268_;
}
v___jp_1259_:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_pu_1258_, v___y_1260_, v___y_1261_);
if (v_pu_1258_ == 0)
{
lean_object* v_funDeclsPure_1263_; lean_object* v___x_1264_; 
v_funDeclsPure_1263_ = lean_ctor_get(v_lctx_1257_, 4);
v___x_1264_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v___x_1262_, v_funDeclsPure_1263_);
return v___x_1264_;
}
else
{
lean_object* v_funDeclsImpure_1265_; lean_object* v___x_1266_; 
v_funDeclsImpure_1265_ = lean_ctor_get(v_lctx_1257_, 5);
v___x_1266_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v___x_1262_, v_funDeclsImpure_1265_);
return v___x_1266_;
}
}
v___jp_1268_:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_DHashMap_Raw_forIn___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_result_1267_, v___y_1269_);
if (v_pu_1258_ == 0)
{
lean_object* v_letDeclsPure_1271_; 
v_letDeclsPure_1271_ = lean_ctor_get(v_lctx_1257_, 2);
v___y_1260_ = v___x_1270_;
v___y_1261_ = v_letDeclsPure_1271_;
goto v___jp_1259_;
}
else
{
lean_object* v_letDeclsImpure_1272_; 
v_letDeclsImpure_1272_ = lean_ctor_get(v_lctx_1257_, 3);
v___y_1260_ = v___x_1270_;
v___y_1261_ = v_letDeclsImpure_1272_;
goto v___jp_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(lean_object* v_lctx_1275_, lean_object* v_pu_1276_){
_start:
{
uint8_t v_pu_boxed_1277_; lean_object* v_res_1278_; 
v_pu_boxed_1277_ = lean_unbox(v_pu_1276_);
v_res_1278_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1275_, v_pu_boxed_1277_);
lean_dec_ref(v_lctx_1275_);
return v_res_1278_;
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
