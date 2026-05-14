// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.ToIRType
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
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_ToIR_addDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_IR_ToIR_addDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
static lean_once_cell_t l_Lean_IR_ToIR_addDecl___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "all local functions should be λ-lifted"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__2 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__2_value;
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.IR.ToIR.lowerCode"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__1 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__1_value;
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Compiler.IR.ToIR"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__0 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__0_value;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__4 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__4_value;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__8;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__10;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__11;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__12;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__13;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_toIR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_toIR___closed__0 = (const lean_object*)&l_Lean_IR_toIR___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__0, &l_Lean_IR_ToIR_M_run___redArg___closed__0_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__1, &l_Lean_IR_ToIR_M_run___redArg___closed__1_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__1);
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__2, &l_Lean_IR_ToIR_M_run___redArg___closed__2_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__2);
v___x_15_ = lean_st_mk_ref(v___x_14_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v___x_15_);
v___x_16_ = lean_apply_4(v_x_10_, v___x_15_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_25_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_25_ == 0)
{
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_st_ref_get(v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_21_);
if (v_isShared_20_ == 0)
{
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_17_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
else
{
lean_dec(v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object* v_x_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_IR_ToIR_M_run___redArg(v_x_26_, v_a_27_, v_a_28_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* v_00_u03b1_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_IR_ToIR_M_run___redArg(v_x_32_, v_a_33_, v_a_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object* v_00_u03b1_37_, lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_IR_ToIR_M_run(v_00_u03b1_37_, v_x_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object* v_msg_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Lean_IR_instInhabitedArg_default;
v___x_45_ = lean_panic_fn_borrowed(v___x_44_, v_msg_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_49_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2));
v___x_50_ = lean_unsigned_to_nat(11u);
v___x_51_ = lean_unsigned_to_nat(163u);
v___x_52_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1));
v___x_53_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0));
v___x_54_ = l_mkPanicMessageWithDecl(v___x_53_, v___x_52_, v___x_51_, v___x_50_, v___x_49_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* v_a_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3);
v___x_58_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_key_59_; lean_object* v_value_60_; lean_object* v_tail_61_; uint8_t v___x_62_; 
v_key_59_ = lean_ctor_get(v_x_56_, 0);
v_value_60_ = lean_ctor_get(v_x_56_, 1);
v_tail_61_ = lean_ctor_get(v_x_56_, 2);
v___x_62_ = l_Lean_instBEqFVarId_beq(v_key_59_, v_a_55_);
if (v___x_62_ == 0)
{
v_x_56_ = v_tail_61_;
goto _start;
}
else
{
lean_inc(v_value_60_);
return v_value_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_a_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_a_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object* v_m_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_buckets_69_; lean_object* v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v_fold_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_buckets_69_ = lean_ctor_get(v_m_67_, 1);
v___x_70_ = lean_array_get_size(v_buckets_69_);
v___x_71_ = l_Lean_instHashableFVarId_hash(v_a_68_);
v___x_72_ = 32ULL;
v___x_73_ = lean_uint64_shift_right(v___x_71_, v___x_72_);
v_fold_74_ = lean_uint64_xor(v___x_71_, v___x_73_);
v___x_75_ = 16ULL;
v___x_76_ = lean_uint64_shift_right(v_fold_74_, v___x_75_);
v___x_77_ = lean_uint64_xor(v_fold_74_, v___x_76_);
v___x_78_ = lean_uint64_to_usize(v___x_77_);
v___x_79_ = lean_usize_of_nat(v___x_70_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_sub(v___x_79_, v___x_80_);
v___x_82_ = lean_usize_land(v___x_78_, v___x_81_);
v___x_83_ = lean_array_uget_borrowed(v_buckets_69_, v___x_82_);
v___x_84_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_a_68_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* v_m_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_m_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_m_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* v_fvarId_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_vars_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_st_ref_get(v_a_89_);
v_vars_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_vars_92_);
lean_dec(v___x_91_);
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_vars_92_, v_fvarId_88_);
lean_dec_ref(v_vars_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* v_fvarId_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec(v_fvarId_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* v_fvarId_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_99_, v_a_100_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* v_fvarId_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_IR_ToIR_getFVarValue(v_fvarId_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec(v_fvarId_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(lean_object* v_msg_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_panic_fn_borrowed(v___x_112_, v_msg_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(lean_object* v_a_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3);
v___x_117_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_key_118_; lean_object* v_value_119_; lean_object* v_tail_120_; uint8_t v___x_121_; 
v_key_118_ = lean_ctor_get(v_x_115_, 0);
v_value_119_ = lean_ctor_get(v_x_115_, 1);
v_tail_120_ = lean_ctor_get(v_x_115_, 2);
v___x_121_ = l_Lean_instBEqFVarId_beq(v_key_118_, v_a_114_);
if (v___x_121_ == 0)
{
v_x_115_ = v_tail_120_;
goto _start;
}
else
{
lean_inc(v_value_119_);
return v_value_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0___boxed(lean_object* v_a_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v_a_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(lean_object* v_m_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_buckets_128_; lean_object* v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v_fold_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_buckets_128_ = lean_ctor_get(v_m_126_, 1);
v___x_129_ = lean_array_get_size(v_buckets_128_);
v___x_130_ = l_Lean_instHashableFVarId_hash(v_a_127_);
v___x_131_ = 32ULL;
v___x_132_ = lean_uint64_shift_right(v___x_130_, v___x_131_);
v_fold_133_ = lean_uint64_xor(v___x_130_, v___x_132_);
v___x_134_ = 16ULL;
v___x_135_ = lean_uint64_shift_right(v_fold_133_, v___x_134_);
v___x_136_ = lean_uint64_xor(v_fold_133_, v___x_135_);
v___x_137_ = lean_uint64_to_usize(v___x_136_);
v___x_138_ = lean_usize_of_nat(v___x_129_);
v___x_139_ = ((size_t)1ULL);
v___x_140_ = lean_usize_sub(v___x_138_, v___x_139_);
v___x_141_ = lean_usize_land(v___x_137_, v___x_140_);
v___x_142_ = lean_array_uget_borrowed(v_buckets_128_, v___x_141_);
v___x_143_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v_a_127_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(lean_object* v_m_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_m_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_m_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* v_fvarId_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; lean_object* v_joinPoints_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_st_ref_get(v_a_148_);
v_joinPoints_151_ = lean_ctor_get(v___x_150_, 1);
lean_inc_ref(v_joinPoints_151_);
lean_dec(v___x_150_);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_joinPoints_151_, v_fvarId_147_);
lean_dec_ref(v_joinPoints_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* v_fvarId_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec(v_fvarId_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* v_fvarId_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_158_, v_a_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* v_fvarId_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_IR_ToIR_getJoinPointValue(v_fvarId_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_fvarId_164_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* v_a_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
else
{
lean_object* v_key_173_; lean_object* v_tail_174_; uint8_t v___x_175_; 
v_key_173_ = lean_ctor_get(v_x_171_, 0);
v_tail_174_ = lean_ctor_get(v_x_171_, 2);
v___x_175_ = l_Lean_instBEqFVarId_beq(v_key_173_, v_a_170_);
if (v___x_175_ == 0)
{
v_x_171_ = v_tail_174_;
goto _start;
}
else
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_177_, lean_object* v_x_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_177_, v_x_178_);
lean_dec(v_x_178_);
lean_dec(v_a_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
return v_x_181_;
}
else
{
lean_object* v_key_183_; lean_object* v_value_184_; lean_object* v_tail_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_208_; 
v_key_183_ = lean_ctor_get(v_x_182_, 0);
v_value_184_ = lean_ctor_get(v_x_182_, 1);
v_tail_185_ = lean_ctor_get(v_x_182_, 2);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_208_ == 0)
{
v___x_187_ = v_x_182_;
v_isShared_188_ = v_isSharedCheck_208_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_tail_185_);
lean_inc(v_value_184_);
lean_inc(v_key_183_);
lean_dec(v_x_182_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_208_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_fold_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_189_ = lean_array_get_size(v_x_181_);
v___x_190_ = l_Lean_instHashableFVarId_hash(v_key_183_);
v___x_191_ = 32ULL;
v___x_192_ = lean_uint64_shift_right(v___x_190_, v___x_191_);
v_fold_193_ = lean_uint64_xor(v___x_190_, v___x_192_);
v___x_194_ = 16ULL;
v___x_195_ = lean_uint64_shift_right(v_fold_193_, v___x_194_);
v___x_196_ = lean_uint64_xor(v_fold_193_, v___x_195_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = lean_usize_of_nat(v___x_189_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v___x_198_, v___x_199_);
v___x_201_ = lean_usize_land(v___x_197_, v___x_200_);
v___x_202_ = lean_array_uget_borrowed(v_x_181_, v___x_201_);
lean_inc(v___x_202_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 2, v___x_202_);
v___x_204_ = v___x_187_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_key_183_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_value_184_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v___x_202_);
v___x_204_ = v_reuseFailAlloc_207_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_array_uset(v_x_181_, v___x_201_, v___x_204_);
v_x_181_ = v___x_205_;
v_x_182_ = v_tail_185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_209_, lean_object* v_source_210_, lean_object* v_target_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_array_get_size(v_source_210_);
v___x_213_ = lean_nat_dec_lt(v_i_209_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec_ref(v_source_210_);
lean_dec(v_i_209_);
return v_target_211_;
}
else
{
lean_object* v_es_214_; lean_object* v___x_215_; lean_object* v_source_216_; lean_object* v_target_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_es_214_ = lean_array_fget(v_source_210_, v_i_209_);
v___x_215_ = lean_box(0);
v_source_216_ = lean_array_fset(v_source_210_, v_i_209_, v___x_215_);
v_target_217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_211_, v_es_214_);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_i_209_, v___x_218_);
lean_dec(v_i_209_);
v_i_209_ = v___x_219_;
v_source_210_ = v_source_216_;
v_target_211_ = v_target_217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object* v_data_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_nbuckets_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_222_ = lean_array_get_size(v_data_221_);
v___x_223_ = lean_unsigned_to_nat(2u);
v_nbuckets_224_ = lean_nat_mul(v___x_222_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_box(0);
v___x_227_ = lean_mk_array(v_nbuckets_224_, v___x_226_);
v___x_228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v___x_225_, v_data_221_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* v_m_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v_size_232_; lean_object* v_buckets_233_; lean_object* v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v_fold_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v_bkt_247_; uint8_t v___x_248_; 
v_size_232_ = lean_ctor_get(v_m_229_, 0);
v_buckets_233_ = lean_ctor_get(v_m_229_, 1);
v___x_234_ = lean_array_get_size(v_buckets_233_);
v___x_235_ = l_Lean_instHashableFVarId_hash(v_a_230_);
v___x_236_ = 32ULL;
v___x_237_ = lean_uint64_shift_right(v___x_235_, v___x_236_);
v_fold_238_ = lean_uint64_xor(v___x_235_, v___x_237_);
v___x_239_ = 16ULL;
v___x_240_ = lean_uint64_shift_right(v_fold_238_, v___x_239_);
v___x_241_ = lean_uint64_xor(v_fold_238_, v___x_240_);
v___x_242_ = lean_uint64_to_usize(v___x_241_);
v___x_243_ = lean_usize_of_nat(v___x_234_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_land(v___x_242_, v___x_245_);
v_bkt_247_ = lean_array_uget_borrowed(v_buckets_233_, v___x_246_);
v___x_248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_230_, v_bkt_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_269_; 
lean_inc_ref(v_buckets_233_);
lean_inc(v_size_232_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_m_229_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_270_ = lean_ctor_get(v_m_229_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_m_229_, 0);
lean_dec(v_unused_271_);
v___x_250_ = v_m_229_;
v_isShared_251_ = v_isSharedCheck_269_;
goto v_resetjp_249_;
}
else
{
lean_dec(v_m_229_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_269_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v_size_x27_253_; lean_object* v___x_254_; lean_object* v_buckets_x27_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v_size_x27_253_ = lean_nat_add(v_size_232_, v___x_252_);
lean_dec(v_size_232_);
lean_inc(v_bkt_247_);
v___x_254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_254_, 0, v_a_230_);
lean_ctor_set(v___x_254_, 1, v_b_231_);
lean_ctor_set(v___x_254_, 2, v_bkt_247_);
v_buckets_x27_255_ = lean_array_uset(v_buckets_233_, v___x_246_, v___x_254_);
v___x_256_ = lean_unsigned_to_nat(4u);
v___x_257_ = lean_nat_mul(v_size_x27_253_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(3u);
v___x_259_ = lean_nat_div(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_array_get_size(v_buckets_x27_255_);
v___x_261_ = lean_nat_dec_le(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
if (v___x_261_ == 0)
{
lean_object* v_val_262_; lean_object* v___x_264_; 
v_val_262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_buckets_x27_255_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_val_262_);
lean_ctor_set(v___x_250_, 0, v_size_x27_253_);
v___x_264_ = v___x_250_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_size_x27_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_val_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
else
{
lean_object* v___x_267_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_buckets_x27_255_);
lean_ctor_set(v___x_250_, 0, v_size_x27_253_);
v___x_267_ = v___x_250_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_size_x27_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_buckets_x27_255_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_dec(v_b_231_);
lean_dec(v_a_230_);
return v_m_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* v_fvarId_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; lean_object* v_vars_276_; lean_object* v_joinPoints_277_; lean_object* v_nextId_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_291_; 
v___x_275_ = lean_st_ref_take(v_a_273_);
v_vars_276_ = lean_ctor_get(v___x_275_, 0);
v_joinPoints_277_ = lean_ctor_get(v___x_275_, 1);
v_nextId_278_ = lean_ctor_get(v___x_275_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_291_ == 0)
{
v___x_280_ = v___x_275_;
v_isShared_281_ = v_isSharedCheck_291_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_nextId_278_);
lean_inc(v_joinPoints_277_);
lean_inc(v_vars_276_);
lean_dec(v___x_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_291_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_inc(v_nextId_278_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_nextId_278_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_276_, v_fvarId_272_, v___x_282_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_nextId_278_, v___x_284_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 2, v___x_285_);
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_287_ = v___x_280_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_joinPoints_277_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_285_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_st_ref_set(v_a_273_, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v_nextId_278_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_292_, v_a_293_);
lean_dec(v_a_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_296_, v_a_297_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_IR_ToIR_bindVar(v_fvarId_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_308_, lean_object* v_m_309_, lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_309_, v_a_310_, v_b_311_);
return v___x_312_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_313_, lean_object* v_a_314_, lean_object* v_x_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_317_, lean_object* v_a_318_, lean_object* v_x_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_317_, v_a_318_, v_x_319_);
lean_dec(v_x_319_);
lean_dec(v_a_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* v_00_u03b2_322_, lean_object* v_data_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_325_, lean_object* v_i_326_, lean_object* v_source_327_, lean_object* v_target_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_326_, v_source_327_, v_target_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_331_, v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_vars_338_; lean_object* v_joinPoints_339_; lean_object* v_nextId_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_352_; 
v___x_337_ = lean_st_ref_take(v_a_335_);
v_vars_338_ = lean_ctor_get(v___x_337_, 0);
v_joinPoints_339_ = lean_ctor_get(v___x_337_, 1);
v_nextId_340_ = lean_ctor_get(v___x_337_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_352_ == 0)
{
v___x_342_ = v___x_337_;
v_isShared_343_ = v_isSharedCheck_352_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_nextId_340_);
lean_inc(v_joinPoints_339_);
lean_inc(v_vars_338_);
lean_dec(v___x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_352_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
lean_inc(v_nextId_340_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_339_, v_fvarId_334_, v_nextId_340_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_nextId_340_, v___x_345_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 2, v___x_346_);
lean_ctor_set(v___x_342_, 1, v___x_344_);
v___x_348_ = v___x_342_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_vars_338_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v___x_346_);
v___x_348_ = v_reuseFailAlloc_351_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_st_ref_set(v_a_335_, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v_nextId_340_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_353_, v_a_354_);
lean_dec(v_a_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_357_, v_a_358_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_vars_373_; lean_object* v_joinPoints_374_; lean_object* v_nextId_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v___x_372_ = lean_st_ref_take(v_a_370_);
v_vars_373_ = lean_ctor_get(v___x_372_, 0);
v_joinPoints_374_ = lean_ctor_get(v___x_372_, 1);
v_nextId_375_ = lean_ctor_get(v___x_372_, 2);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v___x_372_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_nextId_375_);
lean_inc(v_joinPoints_374_);
lean_inc(v_vars_373_);
lean_dec(v___x_372_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = lean_box(1);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_373_, v_fvarId_369_, v___x_379_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_joinPoints_374_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_nextId_375_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_st_ref_set(v_a_370_, v___x_382_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_388_, v_a_389_);
lean_dec(v_a_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_392_, v_a_393_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_IR_ToIR_bindErased(v_fvarId_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_404_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_env_413_; lean_object* v_nextMacroScope_414_; lean_object* v_ngen_415_; lean_object* v_auxDeclNGen_416_; lean_object* v_traceState_417_; lean_object* v_messages_418_; lean_object* v_infoState_419_; lean_object* v_snapshotTasks_420_; lean_object* v_newDecls_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_437_; 
v___x_412_ = lean_st_ref_take(v_a_410_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
v_nextMacroScope_414_ = lean_ctor_get(v___x_412_, 1);
v_ngen_415_ = lean_ctor_get(v___x_412_, 2);
v_auxDeclNGen_416_ = lean_ctor_get(v___x_412_, 3);
v_traceState_417_ = lean_ctor_get(v___x_412_, 4);
v_messages_418_ = lean_ctor_get(v___x_412_, 6);
v_infoState_419_ = lean_ctor_get(v___x_412_, 7);
v_snapshotTasks_420_ = lean_ctor_get(v___x_412_, 8);
v_newDecls_421_ = lean_ctor_get(v___x_412_, 9);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_412_, 5);
lean_dec(v_unused_438_);
v___x_423_ = v___x_412_;
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_newDecls_421_);
lean_inc(v_snapshotTasks_420_);
lean_inc(v_infoState_419_);
lean_inc(v_messages_418_);
lean_inc(v_traceState_417_);
lean_inc(v_auxDeclNGen_416_);
lean_inc(v_ngen_415_);
lean_inc(v_nextMacroScope_414_);
lean_inc(v_env_413_);
lean_dec(v___x_412_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v_toEnvExtension_426_; lean_object* v_asyncMode_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_425_ = l_Lean_IR_declMapExt;
v_toEnvExtension_426_ = lean_ctor_get(v___x_425_, 0);
v_asyncMode_427_ = lean_ctor_get(v_toEnvExtension_426_, 2);
v___x_428_ = lean_box(0);
v___x_429_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_425_, v_env_413_, v_d_409_, v_asyncMode_427_, v___x_428_);
v___x_430_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 5, v___x_430_);
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_432_ = v___x_423_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_nextMacroScope_414_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_ngen_415_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_auxDeclNGen_416_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_traceState_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_messages_418_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_infoState_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_snapshotTasks_420_);
lean_ctor_set(v_reuseFailAlloc_436_, 9, v_newDecls_421_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_set(v_a_410_, v___x_432_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_439_, v_a_440_);
lean_dec(v_a_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_443_, v_a_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_IR_ToIR_addDecl(v_d_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_455_){
_start:
{
switch(lean_obj_tag(v_v_455_))
{
case 0:
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_470_; 
v_val_456_ = lean_ctor_get(v_v_455_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_v_455_);
if (v_isSharedCheck_470_ == 0)
{
v___x_458_ = v_v_455_;
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v_v_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___y_461_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_cstr_to_nat("4294967296");
v___x_467_ = lean_nat_dec_lt(v_val_456_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(8);
v___y_461_ = v___x_468_;
goto v___jp_460_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(12);
v___y_461_ = v___x_469_;
goto v___jp_460_;
}
v___jp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_459_ == 0)
{
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_val_456_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
lean_inc(v___y_461_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___y_461_);
return v___x_464_;
}
}
}
}
case 1:
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_480_; 
v_val_471_ = lean_ctor_get(v_v_455_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_v_455_);
if (v_isSharedCheck_480_ == 0)
{
v___x_473_ = v_v_455_;
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v_v_455_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_val_471_);
v___x_476_ = v_reuseFailAlloc_479_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_box(7);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
}
case 2:
{
uint8_t v_val_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_val_481_ = lean_ctor_get_uint8(v_v_455_, 0);
lean_dec_ref(v_v_455_);
v___x_482_ = lean_uint8_to_nat(v_val_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = lean_box(1);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
return v___x_485_;
}
case 3:
{
uint16_t v_val_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_val_486_ = lean_ctor_get_uint16(v_v_455_, 0);
lean_dec_ref(v_v_455_);
v___x_487_ = lean_uint16_to_nat(v_val_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_box(2);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
case 4:
{
uint32_t v_val_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_val_491_ = lean_ctor_get_uint32(v_v_455_, 0);
lean_dec_ref(v_v_455_);
v___x_492_ = lean_uint32_to_nat(v_val_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
v___x_494_ = lean_box(3);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
case 5:
{
uint64_t v_val_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_val_496_ = lean_ctor_get_uint64(v_v_455_, 0);
lean_dec_ref(v_v_455_);
v___x_497_ = lean_uint64_to_nat(v_val_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = lean_box(4);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
default: 
{
uint64_t v_val_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_val_501_ = lean_ctor_get_uint64(v_v_455_, 0);
lean_dec_ref(v_v_455_);
v___x_502_ = lean_uint64_to_nat(v_val_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = lean_box(5);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
if (lean_obj_tag(v_a_506_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_box(1);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_fvarId_511_; lean_object* v___x_512_; 
v_fvarId_511_ = lean_ctor_get(v_a_506_, 0);
v___x_512_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_511_, v_a_507_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_517_, v_a_518_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_IR_ToIR_lowerArg(v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec(v_a_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_fvarId_532_; lean_object* v_type_533_; uint8_t v_borrow_534_; lean_object* v___x_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
v_fvarId_532_ = lean_ctor_get(v_p_529_, 0);
lean_inc(v_fvarId_532_);
v_type_533_ = lean_ctor_get(v_p_529_, 2);
lean_inc_ref(v_type_533_);
v_borrow_534_ = lean_ctor_get_uint8(v_p_529_, sizeof(void*)*3);
lean_dec_ref(v_p_529_);
v___x_535_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_532_, v_a_530_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = l_Lean_IR_toIRType(v_type_533_);
lean_dec_ref(v_type_533_);
v___x_541_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_541_, 0, v_a_536_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*2, v_borrow_534_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_546_, v_a_547_);
lean_dec(v_a_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_550_, v_a_551_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_IR_ToIR_lowerParam(v_p_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_562_){
_start:
{
lean_object* v_name_563_; lean_object* v_cidx_564_; lean_object* v_size_565_; lean_object* v_usize_566_; lean_object* v_ssize_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_name_563_ = lean_ctor_get(v_i_562_, 0);
v_cidx_564_ = lean_ctor_get(v_i_562_, 1);
v_size_565_ = lean_ctor_get(v_i_562_, 2);
v_usize_566_ = lean_ctor_get(v_i_562_, 3);
v_ssize_567_ = lean_ctor_get(v_i_562_, 4);
v_isSharedCheck_574_ = !lean_is_exclusive(v_i_562_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v_i_562_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_ssize_567_);
lean_inc(v_usize_566_);
lean_inc(v_size_565_);
lean_inc(v_cidx_564_);
lean_inc(v_name_563_);
lean_dec(v_i_562_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_name_563_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_cidx_564_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_size_565_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_usize_566_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_ssize_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_instMonadEIO(lean_box(0));
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_toApplicative_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_617_; 
v___x_583_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_584_ = l_StateRefT_x27_instMonad___redArg(v___x_583_);
v_toApplicative_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_584_, 1);
lean_dec(v_unused_618_);
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_617_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_toApplicative_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_617_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_toFunctor_589_; lean_object* v_toSeq_590_; lean_object* v_toSeqLeft_591_; lean_object* v_toSeqRight_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_615_; 
v_toFunctor_589_ = lean_ctor_get(v_toApplicative_585_, 0);
v_toSeq_590_ = lean_ctor_get(v_toApplicative_585_, 2);
v_toSeqLeft_591_ = lean_ctor_get(v_toApplicative_585_, 3);
v_toSeqRight_592_ = lean_ctor_get(v_toApplicative_585_, 4);
v_isSharedCheck_615_ = !lean_is_exclusive(v_toApplicative_585_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_toApplicative_585_, 1);
lean_dec(v_unused_616_);
v___x_594_ = v_toApplicative_585_;
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_toSeqRight_592_);
lean_inc(v_toSeqLeft_591_);
lean_inc(v_toSeq_590_);
lean_inc(v_toFunctor_589_);
lean_dec(v_toApplicative_585_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_605_; 
v___f_596_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_597_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_589_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_598_, 0, v_toFunctor_589_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_599_, 0, v_toFunctor_589_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___f_598_);
lean_ctor_set(v___x_600_, 1, v___f_599_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeqRight_592_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_602_, 0, v_toSeqLeft_591_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_603_, 0, v_toSeq_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___f_601_);
lean_ctor_set(v___x_594_, 3, v___f_602_);
lean_ctor_set(v___x_594_, 2, v___f_603_);
lean_ctor_set(v___x_594_, 1, v___f_596_);
lean_ctor_set(v___x_594_, 0, v___x_600_);
v___x_605_ = v___x_594_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___f_596_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___f_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v___f_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v___f_601_);
v___x_605_ = v_reuseFailAlloc_614_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___f_597_);
lean_ctor_set(v___x_587_, 0, v___x_605_);
v___x_607_ = v___x_587_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___f_597_);
v___x_607_ = v_reuseFailAlloc_613_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_8612__overap_611_; lean_object* v___x_612_; 
v___x_608_ = l_StateRefT_x27_instMonad___redArg(v___x_607_);
v___x_609_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_610_ = l_instInhabitedOfMonad___redArg(v___x_608_, v___x_609_);
v___x_8612__overap_611_ = lean_panic_fn_borrowed(v___x_610_, v_msg_578_);
lean_dec(v___x_610_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
lean_inc(v___y_579_);
v___x_612_ = lean_apply_4(v___x_8612__overap_611_, v___y_579_, v___y_580_, v___y_581_, lean_box(0));
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_625_, size_t v_i_626_, lean_object* v_bs_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_lt(v_i_626_, v_sz_625_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_bs_627_);
return v___x_631_;
}
else
{
lean_object* v_v_632_; lean_object* v___x_633_; 
v_v_632_ = lean_array_uget_borrowed(v_bs_627_, v_i_626_);
v___x_633_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_632_, v___y_628_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v_bs_x27_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v_bs_x27_636_ = lean_array_uset(v_bs_627_, v_i_626_, v___x_635_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_626_, v___x_637_);
v___x_639_ = lean_array_uset(v_bs_x27_636_, v_i_626_, v_a_634_);
v_i_626_ = v___x_638_;
v_bs_627_ = v___x_639_;
goto _start;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v_bs_627_);
v_a_641_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_633_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_633_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_649_, lean_object* v_i_650_, lean_object* v_bs_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
size_t v_sz_boxed_654_; size_t v_i_boxed_655_; lean_object* v_res_656_; 
v_sz_boxed_654_ = lean_unbox_usize(v_sz_649_);
lean_dec(v_sz_649_);
v_i_boxed_655_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_654_, v_i_boxed_655_, v_bs_651_, v___y_652_);
lean_dec(v___y_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_657_, size_t v_i_658_, lean_object* v_bs_659_, lean_object* v___y_660_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v_bs_659_);
return v___x_663_;
}
else
{
lean_object* v_v_664_; lean_object* v___x_665_; 
v_v_664_ = lean_array_uget_borrowed(v_bs_659_, v_i_658_);
lean_inc(v_v_664_);
v___x_665_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_664_, v___y_660_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v_bs_x27_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref(v___x_665_);
v___x_667_ = lean_unsigned_to_nat(0u);
v_bs_x27_668_ = lean_array_uset(v_bs_659_, v_i_658_, v___x_667_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_658_, v___x_669_);
v___x_671_ = lean_array_uset(v_bs_x27_668_, v_i_658_, v_a_666_);
v_i_658_ = v___x_670_;
v_bs_659_ = v___x_671_;
goto _start;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_bs_659_);
v_a_673_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_665_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_665_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_bs_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
size_t v_sz_boxed_686_; size_t v_i_boxed_687_; lean_object* v_res_688_; 
v_sz_boxed_686_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_687_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_686_, v_i_boxed_687_, v_bs_683_, v___y_684_);
lean_dec(v___y_684_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_689_, lean_object* v_continueLet_690_, lean_object* v_var_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_696_, 0, v_i_689_);
lean_ctor_set(v___x_696_, 1, v_var_691_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
v___x_697_ = lean_apply_5(v_continueLet_690_, v___x_696_, v___y_692_, v___y_693_, v___y_694_, lean_box(0));
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_698_, lean_object* v_continueLet_699_, lean_object* v_var_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_698_, v_continueLet_699_, v_var_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_706_, lean_object* v_offset_707_, lean_object* v_continueLet_708_, lean_object* v_var_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_714_, 0, v_n_706_);
lean_ctor_set(v___x_714_, 1, v_offset_707_);
lean_ctor_set(v___x_714_, 2, v_var_709_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
v___x_715_ = lean_apply_5(v_continueLet_708_, v___x_714_, v___y_710_, v___y_711_, v___y_712_, lean_box(0));
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_716_, lean_object* v_offset_717_, lean_object* v_continueLet_718_, lean_object* v_var_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_716_, v_offset_717_, v_continueLet_718_, v_var_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_725_, lean_object* v_continueLet_726_, lean_object* v_var_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v_n_725_);
lean_ctor_set(v___x_732_, 1, v_var_727_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
v___x_733_ = lean_apply_5(v_continueLet_726_, v___x_732_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_734_, lean_object* v_continueLet_735_, lean_object* v_var_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_734_, v_continueLet_735_, v_var_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_742_, lean_object* v_var_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_748_, 0, v_var_743_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_744_);
v___x_749_ = lean_apply_5(v_continueLet_742_, v___x_748_, v___y_744_, v___y_745_, v___y_746_, lean_box(0));
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_750_, lean_object* v_var_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_750_, v_var_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_757_, lean_object* v_continueLet_758_, lean_object* v_var_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_764_, 0, v_i_757_);
lean_ctor_set(v___x_764_, 1, v_var_759_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
v___x_765_ = lean_apply_5(v_continueLet_758_, v___x_764_, v___y_760_, v___y_761_, v___y_762_, lean_box(0));
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_766_, lean_object* v_continueLet_767_, lean_object* v_var_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_766_, v_continueLet_767_, v_var_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_774_, lean_object* v_continueLet_775_, lean_object* v_var_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = l_Lean_IR_toIRType(v_ty_774_);
v___x_782_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_var_776_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
v___x_783_ = lean_apply_5(v_continueLet_775_, v___x_782_, v___y_777_, v___y_778_, v___y_779_, lean_box(0));
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_784_, lean_object* v_continueLet_785_, lean_object* v_var_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_784_, v_continueLet_785_, v_var_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v_ty_784_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_792_, lean_object* v_i_793_, uint8_t v_updateHeader_794_, lean_object* v_continueLet_795_, lean_object* v_var_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
size_t v_sz_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_sz_801_ = lean_array_size(v_args_792_);
v___x_802_ = ((size_t)0ULL);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_801_, v___x_802_, v_args_792_, v___y_797_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v_name_805_; lean_object* v_cidx_806_; lean_object* v_size_807_; lean_object* v_usize_808_; lean_object* v_ssize_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v_name_805_ = lean_ctor_get(v_i_793_, 0);
v_cidx_806_ = lean_ctor_get(v_i_793_, 1);
v_size_807_ = lean_ctor_get(v_i_793_, 2);
v_usize_808_ = lean_ctor_get(v_i_793_, 3);
v_ssize_809_ = lean_ctor_get(v_i_793_, 4);
v_isSharedCheck_818_ = !lean_is_exclusive(v_i_793_);
if (v_isSharedCheck_818_ == 0)
{
v___x_811_ = v_i_793_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_ssize_809_);
lean_inc(v_usize_808_);
lean_inc(v_size_807_);
lean_inc(v_cidx_806_);
lean_inc(v_name_805_);
lean_dec(v_i_793_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_name_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_cidx_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_size_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_usize_808_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_ssize_809_);
v___x_814_ = v_reuseFailAlloc_817_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_815_, 0, v_var_796_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
lean_ctor_set(v___x_815_, 2, v_a_804_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*3, v_updateHeader_794_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
v___x_816_ = lean_apply_5(v_continueLet_795_, v___x_815_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
return v___x_816_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_var_796_);
lean_dec_ref(v_continueLet_795_);
lean_dec_ref(v_i_793_);
v_a_819_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_803_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_803_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_827_, lean_object* v_i_828_, lean_object* v_updateHeader_829_, lean_object* v_continueLet_830_, lean_object* v_var_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_updateHeader_9654__boxed_836_; lean_object* v_res_837_; 
v_updateHeader_9654__boxed_836_ = lean_unbox(v_updateHeader_829_);
v_res_837_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_827_, v_i_828_, v_updateHeader_9654__boxed_836_, v_continueLet_830_, v_var_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_838_, lean_object* v_var_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_844_, 0, v_var_839_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
v___x_845_ = lean_apply_5(v_continueLet_838_, v___x_844_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_846_, lean_object* v_var_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_846_, v_var_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_853_, lean_object* v_continueLet_854_, lean_object* v_id_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; 
v_sz_860_ = lean_array_size(v_args_853_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_860_, v___x_861_, v_args_853_, v___y_856_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_864_, 0, v_id_855_);
lean_ctor_set(v___x_864_, 1, v_a_863_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
v___x_865_ = lean_apply_5(v_continueLet_854_, v___x_864_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_id_855_);
lean_dec_ref(v_continueLet_854_);
v_a_866_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_862_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_874_, lean_object* v_continueLet_875_, lean_object* v_id_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_874_, v_continueLet_875_, v_id_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_882_, lean_object* v_k_883_, lean_object* v_type_884_, lean_object* v_e_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_882_, v___y_886_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = l_Lean_IR_ToIR_lowerCode(v_k_883_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_901_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_897_, 0, v_a_891_);
lean_ctor_set(v___x_897_, 1, v_type_884_);
lean_ctor_set(v___x_897_, 2, v_e_885_);
lean_ctor_set(v___x_897_, 3, v_a_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_897_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_dec(v_a_891_);
lean_dec_ref(v_e_885_);
lean_dec(v_type_884_);
return v___x_892_;
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_e_885_);
lean_dec(v_type_884_);
lean_dec_ref(v_k_883_);
v_a_902_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_890_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_890_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_910_, lean_object* v_k_911_, lean_object* v_type_912_, lean_object* v_e_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_910_, v_k_911_, v_type_912_, v_e_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_919_, lean_object* v_k_920_, lean_object* v_fvarId_921_, lean_object* v_f_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_921_, v_a_923_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref(v___x_927_);
if (lean_obj_tag(v_a_928_) == 0)
{
lean_object* v_id_929_; lean_object* v___x_930_; 
lean_dec_ref(v_k_920_);
lean_dec_ref(v_decl_919_);
v_id_929_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_id_929_);
lean_dec_ref(v_a_928_);
lean_inc(v_a_925_);
lean_inc_ref(v_a_924_);
lean_inc(v_a_923_);
v___x_930_ = lean_apply_5(v_f_922_, v_id_929_, v_a_923_, v_a_924_, v_a_925_, lean_box(0));
return v___x_930_;
}
else
{
lean_object* v___x_931_; 
lean_dec_ref(v_f_922_);
v___x_931_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_919_, v_k_920_, v_a_923_, v_a_924_, v_a_925_);
return v___x_931_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_f_922_);
lean_dec_ref(v_k_920_);
lean_dec_ref(v_decl_919_);
v_a_932_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_927_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_940_, lean_object* v_k_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_fvarId_946_; lean_object* v_type_947_; lean_object* v_value_948_; lean_object* v_type_949_; lean_object* v_continueLet_950_; 
v_fvarId_946_ = lean_ctor_get(v_decl_940_, 0);
v_type_947_ = lean_ctor_get(v_decl_940_, 2);
v_value_948_ = lean_ctor_get(v_decl_940_, 3);
lean_inc(v_value_948_);
v_type_949_ = l_Lean_IR_toIRType(v_type_947_);
lean_inc(v_type_949_);
lean_inc_ref(v_k_941_);
lean_inc(v_fvarId_946_);
v_continueLet_950_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_950_, 0, v_fvarId_946_);
lean_closure_set(v_continueLet_950_, 1, v_k_941_);
lean_closure_set(v_continueLet_950_, 2, v_type_949_);
switch(lean_obj_tag(v_value_948_))
{
case 0:
{
lean_object* v_value_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_961_; 
lean_inc(v_fvarId_946_);
lean_dec_ref(v_continueLet_950_);
lean_dec_ref(v_decl_940_);
v_value_951_ = lean_ctor_get(v_value_948_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_value_948_);
if (v_isSharedCheck_961_ == 0)
{
v___x_953_ = v_value_948_;
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_value_951_);
lean_dec(v_value_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_fst_956_; lean_object* v___x_958_; 
v___x_955_ = l_Lean_IR_ToIR_lowerLitValue(v_value_951_);
v_fst_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_fst_956_);
lean_dec_ref(v___x_955_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 11);
lean_ctor_set(v___x_953_, 0, v_fst_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_fst_956_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_946_, v_k_941_, v_type_949_, v___x_958_, v_a_942_, v_a_943_, v_a_944_);
return v___x_959_;
}
}
}
case 1:
{
lean_object* v___x_962_; 
lean_dec_ref(v_continueLet_950_);
lean_dec(v_type_949_);
v___x_962_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_940_, v_k_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_962_;
}
case 4:
{
lean_object* v_fvarId_963_; lean_object* v_args_964_; lean_object* v___f_965_; lean_object* v___x_966_; 
lean_dec(v_type_949_);
v_fvarId_963_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_fvarId_963_);
v_args_964_ = lean_ctor_get(v_value_948_, 1);
lean_inc_ref(v_args_964_);
lean_dec_ref(v_value_948_);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_965_, 0, v_args_964_);
lean_closure_set(v___f_965_, 1, v_continueLet_950_);
v___x_966_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_fvarId_963_, v___f_965_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_fvarId_963_);
return v___x_966_;
}
case 5:
{
lean_object* v_i_967_; lean_object* v_args_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1000_; 
lean_inc(v_fvarId_946_);
lean_dec_ref(v_continueLet_950_);
lean_dec_ref(v_decl_940_);
v_i_967_ = lean_ctor_get(v_value_948_, 0);
v_args_968_ = lean_ctor_get(v_value_948_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_value_948_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_970_ = v_value_948_;
v_isShared_971_ = v_isSharedCheck_1000_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_args_968_);
lean_inc(v_i_967_);
lean_dec(v_value_948_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1000_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
size_t v_sz_972_; size_t v___x_973_; lean_object* v___x_974_; 
v_sz_972_ = lean_array_size(v_args_968_);
v___x_973_ = ((size_t)0ULL);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_972_, v___x_973_, v_args_968_, v_a_942_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v_name_976_; lean_object* v_cidx_977_; lean_object* v_size_978_; lean_object* v_usize_979_; lean_object* v_ssize_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_991_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v___x_974_);
v_name_976_ = lean_ctor_get(v_i_967_, 0);
v_cidx_977_ = lean_ctor_get(v_i_967_, 1);
v_size_978_ = lean_ctor_get(v_i_967_, 2);
v_usize_979_ = lean_ctor_get(v_i_967_, 3);
v_ssize_980_ = lean_ctor_get(v_i_967_, 4);
v_isSharedCheck_991_ = !lean_is_exclusive(v_i_967_);
if (v_isSharedCheck_991_ == 0)
{
v___x_982_ = v_i_967_;
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_ssize_980_);
lean_inc(v_usize_979_);
lean_inc(v_size_978_);
lean_inc(v_cidx_977_);
lean_inc(v_name_976_);
lean_dec(v_i_967_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_name_976_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_cidx_977_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_size_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_usize_979_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_ssize_980_);
v___x_985_ = v_reuseFailAlloc_990_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 0);
lean_ctor_set(v___x_970_, 1, v_a_975_);
lean_ctor_set(v___x_970_, 0, v___x_985_);
v___x_987_ = v___x_970_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_a_975_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_946_, v_k_941_, v_type_949_, v___x_987_, v_a_942_, v_a_943_, v_a_944_);
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_del_object(v___x_970_);
lean_dec_ref(v_i_967_);
lean_dec(v_type_949_);
lean_dec(v_fvarId_946_);
lean_dec_ref(v_k_941_);
v_a_992_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_974_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_974_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1001_; lean_object* v_var_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; 
lean_dec(v_type_949_);
v_i_1001_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_i_1001_);
v_var_1002_ = lean_ctor_get(v_value_948_, 1);
lean_inc(v_var_1002_);
lean_dec_ref(v_value_948_);
v___f_1003_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1003_, 0, v_i_1001_);
lean_closure_set(v___f_1003_, 1, v_continueLet_950_);
v___x_1004_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_var_1002_, v___f_1003_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_var_1002_);
return v___x_1004_;
}
case 7:
{
lean_object* v_i_1005_; lean_object* v_var_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; 
lean_dec(v_type_949_);
v_i_1005_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_i_1005_);
v_var_1006_ = lean_ctor_get(v_value_948_, 1);
lean_inc(v_var_1006_);
lean_dec_ref(v_value_948_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1007_, 0, v_i_1005_);
lean_closure_set(v___f_1007_, 1, v_continueLet_950_);
v___x_1008_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_var_1006_, v___f_1007_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_var_1006_);
return v___x_1008_;
}
case 8:
{
lean_object* v_n_1009_; lean_object* v_offset_1010_; lean_object* v_var_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
lean_dec(v_type_949_);
v_n_1009_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_n_1009_);
v_offset_1010_ = lean_ctor_get(v_value_948_, 1);
lean_inc(v_offset_1010_);
v_var_1011_ = lean_ctor_get(v_value_948_, 2);
lean_inc(v_var_1011_);
lean_dec_ref(v_value_948_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1012_, 0, v_n_1009_);
lean_closure_set(v___f_1012_, 1, v_offset_1010_);
lean_closure_set(v___f_1012_, 2, v_continueLet_950_);
v___x_1013_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_var_1011_, v___f_1012_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_var_1011_);
return v___x_1013_;
}
case 9:
{
lean_object* v_fn_1014_; lean_object* v_args_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1035_; 
lean_inc(v_fvarId_946_);
lean_dec_ref(v_continueLet_950_);
lean_dec_ref(v_decl_940_);
v_fn_1014_ = lean_ctor_get(v_value_948_, 0);
v_args_1015_ = lean_ctor_get(v_value_948_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_value_948_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1017_ = v_value_948_;
v_isShared_1018_ = v_isSharedCheck_1035_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_args_1015_);
lean_inc(v_fn_1014_);
lean_dec(v_value_948_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1035_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
size_t v_sz_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v_sz_1019_ = lean_array_size(v_args_1015_);
v___x_1020_ = ((size_t)0ULL);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1019_, v___x_1020_, v_args_1015_, v_a_942_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 6);
lean_ctor_set(v___x_1017_, 1, v_a_1022_);
v___x_1024_ = v___x_1017_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_fn_1014_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_a_1022_);
v___x_1024_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_946_, v_k_941_, v_type_949_, v___x_1024_, v_a_942_, v_a_943_, v_a_944_);
return v___x_1025_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_del_object(v___x_1017_);
lean_dec(v_fn_1014_);
lean_dec(v_type_949_);
lean_dec(v_fvarId_946_);
lean_dec_ref(v_k_941_);
v_a_1027_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1036_; lean_object* v_args_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1057_; 
lean_inc(v_fvarId_946_);
lean_dec_ref(v_continueLet_950_);
lean_dec_ref(v_decl_940_);
v_fn_1036_ = lean_ctor_get(v_value_948_, 0);
v_args_1037_ = lean_ctor_get(v_value_948_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_value_948_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1039_ = v_value_948_;
v_isShared_1040_ = v_isSharedCheck_1057_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_args_1037_);
lean_inc(v_fn_1036_);
lean_dec(v_value_948_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1057_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
size_t v_sz_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v_sz_1041_ = lean_array_size(v_args_1037_);
v___x_1042_ = ((size_t)0ULL);
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1041_, v___x_1042_, v_args_1037_, v_a_942_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 7);
lean_ctor_set(v___x_1039_, 1, v_a_1044_);
v___x_1046_ = v___x_1039_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_fn_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_a_1044_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_946_, v_k_941_, v_type_949_, v___x_1046_, v_a_942_, v_a_943_, v_a_944_);
return v___x_1047_;
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_del_object(v___x_1039_);
lean_dec(v_fn_1036_);
lean_dec(v_type_949_);
lean_dec(v_fvarId_946_);
lean_dec_ref(v_k_941_);
v_a_1049_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1043_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1043_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1058_; lean_object* v_var_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; 
lean_dec(v_type_949_);
v_n_1058_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_n_1058_);
v_var_1059_ = lean_ctor_get(v_value_948_, 1);
lean_inc(v_var_1059_);
lean_dec_ref(v_value_948_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1060_, 0, v_n_1058_);
lean_closure_set(v___f_1060_, 1, v_continueLet_950_);
v___x_1061_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_var_1059_, v___f_1060_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_var_1059_);
return v___x_1061_;
}
case 12:
{
lean_object* v_var_1062_; lean_object* v_i_1063_; uint8_t v_updateHeader_1064_; lean_object* v_args_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; 
lean_dec(v_type_949_);
v_var_1062_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_var_1062_);
v_i_1063_ = lean_ctor_get(v_value_948_, 1);
lean_inc_ref(v_i_1063_);
v_updateHeader_1064_ = lean_ctor_get_uint8(v_value_948_, sizeof(void*)*3);
v_args_1065_ = lean_ctor_get(v_value_948_, 2);
lean_inc_ref(v_args_1065_);
lean_dec_ref(v_value_948_);
v___x_1066_ = lean_box(v_updateHeader_1064_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1067_, 0, v_args_1065_);
lean_closure_set(v___f_1067_, 1, v_i_1063_);
lean_closure_set(v___f_1067_, 2, v___x_1066_);
lean_closure_set(v___f_1067_, 3, v_continueLet_950_);
v___x_1068_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_var_1062_, v___f_1067_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_var_1062_);
return v___x_1068_;
}
case 13:
{
lean_object* v_ty_1069_; lean_object* v_fvarId_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; 
lean_dec(v_type_949_);
v_ty_1069_ = lean_ctor_get(v_value_948_, 0);
lean_inc_ref(v_ty_1069_);
v_fvarId_1070_ = lean_ctor_get(v_value_948_, 1);
lean_inc(v_fvarId_1070_);
lean_dec_ref(v_value_948_);
v___f_1071_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1071_, 0, v_ty_1069_);
lean_closure_set(v___f_1071_, 1, v_continueLet_950_);
v___x_1072_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_fvarId_1070_, v___f_1071_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_fvarId_1070_);
return v___x_1072_;
}
case 14:
{
lean_object* v_fvarId_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; 
lean_dec(v_type_949_);
v_fvarId_1073_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_fvarId_1073_);
lean_dec_ref(v_value_948_);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1074_, 0, v_continueLet_950_);
v___x_1075_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_fvarId_1073_, v___f_1074_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_fvarId_1073_);
return v___x_1075_;
}
default: 
{
lean_object* v_fvarId_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
lean_dec(v_type_949_);
v_fvarId_1076_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_fvarId_1076_);
lean_dec_ref(v_value_948_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1077_, 0, v_continueLet_950_);
v___x_1078_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_940_, v_k_941_, v_fvarId_1076_, v___f_1077_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_fvarId_1076_);
return v___x_1078_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1083_ = lean_unsigned_to_nat(15u);
v___x_1084_ = lean_unsigned_to_nat(128u);
v___x_1085_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1086_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1087_ = l_mkPanicMessageWithDecl(v___x_1086_, v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
if (lean_obj_tag(v_a_1088_) == 1)
{
lean_object* v_info_1093_; lean_object* v_code_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1130_; 
v_info_1093_ = lean_ctor_get(v_a_1088_, 0);
v_code_1094_ = lean_ctor_get(v_a_1088_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1096_ = v_a_1088_;
v_isShared_1097_ = v_isSharedCheck_1130_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_code_1094_);
lean_inc(v_info_1093_);
lean_dec(v_a_1088_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1130_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_IR_ToIR_lowerCode(v_code_1094_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1121_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1121_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1121_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_name_1103_; lean_object* v_cidx_1104_; lean_object* v_size_1105_; lean_object* v_usize_1106_; lean_object* v_ssize_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1120_; 
v_name_1103_ = lean_ctor_get(v_info_1093_, 0);
v_cidx_1104_ = lean_ctor_get(v_info_1093_, 1);
v_size_1105_ = lean_ctor_get(v_info_1093_, 2);
v_usize_1106_ = lean_ctor_get(v_info_1093_, 3);
v_ssize_1107_ = lean_ctor_get(v_info_1093_, 4);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_info_1093_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1109_ = v_info_1093_;
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_ssize_1107_);
lean_inc(v_usize_1106_);
lean_inc(v_size_1105_);
lean_inc(v_cidx_1104_);
lean_inc(v_name_1103_);
lean_dec(v_info_1093_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_name_1103_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_cidx_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_size_1105_);
lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_usize_1106_);
lean_ctor_set(v_reuseFailAlloc_1119_, 4, v_ssize_1107_);
v___x_1112_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 0);
lean_ctor_set(v___x_1096_, 1, v_a_1099_);
lean_ctor_set(v___x_1096_, 0, v___x_1112_);
v___x_1114_ = v___x_1096_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_a_1099_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1114_);
v___x_1116_ = v___x_1101_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1096_);
lean_dec_ref(v_info_1093_);
v_a_1122_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1098_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1098_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
else
{
lean_object* v_code_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_code_1131_ = lean_ctor_get(v_a_1088_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_a_1088_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_code_1131_);
lean_dec(v_a_1088_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_IR_ToIR_lowerCode(v_code_1131_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1146_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 0, v_a_1136_);
v___x_1141_ = v___x_1133_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_del_object(v___x_1133_);
v_a_1147_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1135_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1135_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1156_, size_t v_i_1157_, lean_object* v_bs_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1157_, v_sz_1156_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_bs_1158_);
return v___x_1164_;
}
else
{
lean_object* v_v_1165_; lean_object* v___x_1166_; 
v_v_1165_ = lean_array_uget_borrowed(v_bs_1158_, v_i_1157_);
lean_inc(v_v_1165_);
v___x_1166_ = l_Lean_IR_ToIR_lowerAlt(v_v_1165_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v_bs_x27_1169_; size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = lean_unsigned_to_nat(0u);
v_bs_x27_1169_ = lean_array_uset(v_bs_1158_, v_i_1157_, v___x_1168_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1157_, v___x_1170_);
v___x_1172_ = lean_array_uset(v_bs_x27_1169_, v_i_1157_, v_a_1167_);
v_i_1157_ = v___x_1171_;
v_bs_1158_ = v___x_1172_;
goto _start;
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_bs_1158_);
v_a_1174_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1166_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1166_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1183_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1184_ = lean_unsigned_to_nat(53u);
v___x_1185_ = lean_unsigned_to_nat(95u);
v___x_1186_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1187_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1188_ = l_mkPanicMessageWithDecl(v___x_1187_, v___x_1186_, v___x_1185_, v___x_1184_, v___x_1183_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1189_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1190_ = lean_unsigned_to_nat(44u);
v___x_1191_ = lean_unsigned_to_nat(106u);
v___x_1192_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1193_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1194_ = l_mkPanicMessageWithDecl(v___x_1193_, v___x_1192_, v___x_1191_, v___x_1190_, v___x_1189_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1195_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1196_ = lean_unsigned_to_nat(44u);
v___x_1197_ = lean_unsigned_to_nat(114u);
v___x_1198_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1199_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1200_ = l_mkPanicMessageWithDecl(v___x_1199_, v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1202_ = lean_unsigned_to_nat(34u);
v___x_1203_ = lean_unsigned_to_nat(113u);
v___x_1204_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1205_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1206_ = l_mkPanicMessageWithDecl(v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1207_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1208_ = lean_unsigned_to_nat(44u);
v___x_1209_ = lean_unsigned_to_nat(110u);
v___x_1210_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1211_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1212_ = l_mkPanicMessageWithDecl(v___x_1211_, v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1213_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1214_ = lean_unsigned_to_nat(34u);
v___x_1215_ = lean_unsigned_to_nat(109u);
v___x_1216_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1217_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1218_ = l_mkPanicMessageWithDecl(v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1219_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1220_ = lean_unsigned_to_nat(41u);
v___x_1221_ = lean_unsigned_to_nat(117u);
v___x_1222_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1223_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1224_ = l_mkPanicMessageWithDecl(v___x_1223_, v___x_1222_, v___x_1221_, v___x_1220_, v___x_1219_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1225_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1226_ = lean_unsigned_to_nat(41u);
v___x_1227_ = lean_unsigned_to_nat(120u);
v___x_1228_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1229_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1230_ = l_mkPanicMessageWithDecl(v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_, v___x_1225_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1231_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1232_ = lean_unsigned_to_nat(41u);
v___x_1233_ = lean_unsigned_to_nat(123u);
v___x_1234_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1235_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1236_ = l_mkPanicMessageWithDecl(v___x_1235_, v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1237_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1238_ = lean_unsigned_to_nat(41u);
v___x_1239_ = lean_unsigned_to_nat(126u);
v___x_1240_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1241_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1242_ = l_mkPanicMessageWithDecl(v___x_1241_, v___x_1240_, v___x_1239_, v___x_1238_, v___x_1237_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
switch(lean_obj_tag(v_c_1243_))
{
case 0:
{
lean_object* v_decl_1248_; lean_object* v_k_1249_; lean_object* v___x_1250_; 
v_decl_1248_ = lean_ctor_get(v_c_1243_, 0);
lean_inc_ref(v_decl_1248_);
v_k_1249_ = lean_ctor_get(v_c_1243_, 1);
lean_inc_ref(v_k_1249_);
lean_dec_ref(v_c_1243_);
v___x_1250_ = l_Lean_IR_ToIR_lowerLet(v_decl_1248_, v_k_1249_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1250_;
}
case 1:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref(v_c_1243_);
v___x_1251_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1252_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1251_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1252_;
}
case 2:
{
lean_object* v_decl_1253_; lean_object* v_k_1254_; lean_object* v_fvarId_1255_; lean_object* v_params_1256_; lean_object* v_value_1257_; lean_object* v___x_1258_; 
v_decl_1253_ = lean_ctor_get(v_c_1243_, 0);
lean_inc_ref(v_decl_1253_);
v_k_1254_ = lean_ctor_get(v_c_1243_, 1);
lean_inc_ref(v_k_1254_);
lean_dec_ref(v_c_1243_);
v_fvarId_1255_ = lean_ctor_get(v_decl_1253_, 0);
lean_inc(v_fvarId_1255_);
v_params_1256_ = lean_ctor_get(v_decl_1253_, 2);
lean_inc_ref(v_params_1256_);
v_value_1257_ = lean_ctor_get(v_decl_1253_, 4);
lean_inc_ref(v_value_1257_);
lean_dec_ref(v_decl_1253_);
v___x_1258_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1255_, v_a_1244_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; size_t v_sz_1260_; size_t v___x_1261_; lean_object* v___x_1262_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v_sz_1260_ = lean_array_size(v_params_1256_);
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1260_, v___x_1261_, v_params_1256_, v_a_1244_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = l_Lean_IR_ToIR_lowerCode(v_value_1257_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = l_Lean_IR_ToIR_lowerCode(v_k_1254_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1259_);
lean_ctor_set(v___x_1271_, 1, v_a_1263_);
lean_ctor_set(v___x_1271_, 2, v_a_1265_);
lean_ctor_set(v___x_1271_, 3, v_a_1267_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
else
{
lean_dec(v_a_1265_);
lean_dec(v_a_1263_);
lean_dec(v_a_1259_);
return v___x_1266_;
}
}
else
{
lean_dec(v_a_1263_);
lean_dec(v_a_1259_);
lean_dec_ref(v_k_1254_);
return v___x_1264_;
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_a_1259_);
lean_dec_ref(v_value_1257_);
lean_dec_ref(v_k_1254_);
v_a_1276_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1262_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1262_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_value_1257_);
lean_dec_ref(v_params_1256_);
lean_dec_ref(v_k_1254_);
v_a_1284_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1258_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1258_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1292_; lean_object* v_args_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1329_; 
v_fvarId_1292_ = lean_ctor_get(v_c_1243_, 0);
v_args_1293_ = lean_ctor_get(v_c_1243_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1295_ = v_c_1243_;
v_isShared_1296_ = v_isSharedCheck_1329_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_args_1293_);
lean_inc(v_fvarId_1292_);
lean_dec(v_c_1243_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1329_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1292_, v_a_1244_);
lean_dec(v_fvarId_1292_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v_sz_1299_ = lean_array_size(v_args_1293_);
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1299_, v___x_1300_, v_args_1293_, v_a_1244_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1312_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1312_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1312_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 11);
lean_ctor_set(v___x_1295_, 1, v_a_1302_);
lean_ctor_set(v___x_1295_, 0, v_a_1298_);
v___x_1307_ = v___x_1295_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1298_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1307_);
v___x_1309_ = v___x_1304_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_a_1298_);
lean_del_object(v___x_1295_);
v_a_1313_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1301_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1301_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_del_object(v___x_1295_);
lean_dec_ref(v_args_1293_);
v_a_1321_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1297_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1297_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1330_; lean_object* v_typeName_1331_; lean_object* v_discr_1332_; lean_object* v_alts_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1373_; 
v_cases_1330_ = lean_ctor_get(v_c_1243_, 0);
lean_inc_ref(v_cases_1330_);
lean_dec_ref(v_c_1243_);
v_typeName_1331_ = lean_ctor_get(v_cases_1330_, 0);
v_discr_1332_ = lean_ctor_get(v_cases_1330_, 2);
v_alts_1333_ = lean_ctor_get(v_cases_1330_, 3);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_cases_1330_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_cases_1330_, 1);
lean_dec(v_unused_1374_);
v___x_1335_ = v_cases_1330_;
v_isShared_1336_ = v_isSharedCheck_1373_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_alts_1333_);
lean_inc(v_discr_1332_);
lean_inc(v_typeName_1331_);
lean_dec(v_cases_1330_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1373_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1332_, v_a_1244_);
lean_dec(v_discr_1332_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
if (lean_obj_tag(v_a_1338_) == 0)
{
lean_object* v_id_1339_; size_t v_sz_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v_id_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_id_1339_);
lean_dec_ref(v_a_1338_);
v_sz_1340_ = lean_array_size(v_alts_1333_);
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1340_, v___x_1341_, v_alts_1333_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1354_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = l_Lean_IR_nameToIRType(v_typeName_1331_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 9);
lean_ctor_set(v___x_1335_, 3, v_a_1343_);
lean_ctor_set(v___x_1335_, 2, v___x_1347_);
lean_ctor_set(v___x_1335_, 1, v_id_1339_);
v___x_1349_ = v___x_1335_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_typeName_1331_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_id_1339_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_a_1343_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_id_1339_);
lean_del_object(v___x_1335_);
lean_dec(v_typeName_1331_);
v_a_1355_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1342_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1342_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v_a_1338_);
lean_del_object(v___x_1335_);
lean_dec_ref(v_alts_1333_);
lean_dec(v_typeName_1331_);
v___x_1363_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1364_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1363_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1364_;
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1335_);
lean_dec_ref(v_alts_1333_);
lean_dec(v_typeName_1331_);
v_a_1365_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1337_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1337_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1399_; 
v_fvarId_1375_ = lean_ctor_get(v_c_1243_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1377_ = v_c_1243_;
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_fvarId_1375_);
lean_dec(v_c_1243_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1375_, v_a_1244_);
lean_dec(v_fvarId_1375_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1390_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 10);
lean_ctor_set(v___x_1377_, 0, v_a_1380_);
v___x_1385_ = v___x_1377_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1377_);
v_a_1391_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1379_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1379_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_isSharedCheck_1407_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_c_1243_, 0);
lean_dec(v_unused_1408_);
v___x_1401_ = v_c_1243_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_dec(v_c_1243_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(12);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
case 7:
{
lean_object* v_fvarId_1409_; lean_object* v_i_1410_; lean_object* v_y_1411_; lean_object* v_k_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1451_; 
v_fvarId_1409_ = lean_ctor_get(v_c_1243_, 0);
v_i_1410_ = lean_ctor_get(v_c_1243_, 1);
v_y_1411_ = lean_ctor_get(v_c_1243_, 2);
v_k_1412_ = lean_ctor_get(v_c_1243_, 3);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1414_ = v_c_1243_;
v_isShared_1415_ = v_isSharedCheck_1451_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_k_1412_);
lean_inc(v_y_1411_);
lean_inc(v_i_1410_);
lean_inc(v_fvarId_1409_);
lean_dec(v_c_1243_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1451_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1411_, v_a_1244_);
lean_dec(v_y_1411_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1409_, v_a_1244_);
lean_dec(v_fvarId_1409_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
if (lean_obj_tag(v_a_1419_) == 0)
{
lean_object* v_id_1420_; lean_object* v___x_1421_; 
v_id_1420_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_id_1420_);
lean_dec_ref(v_a_1419_);
v___x_1421_ = l_Lean_IR_ToIR_lowerCode(v_k_1412_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1432_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1432_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1432_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 2);
lean_ctor_set(v___x_1414_, 3, v_a_1422_);
lean_ctor_set(v___x_1414_, 2, v_a_1417_);
lean_ctor_set(v___x_1414_, 0, v_id_1420_);
v___x_1427_ = v___x_1414_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_id_1420_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_i_1410_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_a_1417_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1427_);
v___x_1429_ = v___x_1424_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_dec(v_id_1420_);
lean_dec(v_a_1417_);
lean_del_object(v___x_1414_);
lean_dec(v_i_1410_);
return v___x_1421_;
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_a_1419_);
lean_dec(v_a_1417_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_k_1412_);
lean_dec(v_i_1410_);
v___x_1433_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1434_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1433_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1434_;
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1417_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_k_1412_);
lean_dec(v_i_1410_);
v_a_1435_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1418_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1418_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_del_object(v___x_1414_);
lean_dec_ref(v_k_1412_);
lean_dec(v_i_1410_);
lean_dec(v_fvarId_1409_);
v_a_1443_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1416_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1416_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1452_; lean_object* v_i_1453_; lean_object* v_y_1454_; lean_object* v_k_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1497_; 
v_fvarId_1452_ = lean_ctor_get(v_c_1243_, 0);
v_i_1453_ = lean_ctor_get(v_c_1243_, 1);
v_y_1454_ = lean_ctor_get(v_c_1243_, 2);
v_k_1455_ = lean_ctor_get(v_c_1243_, 3);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1457_ = v_c_1243_;
v_isShared_1458_ = v_isSharedCheck_1497_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_k_1455_);
lean_inc(v_y_1454_);
lean_inc(v_i_1453_);
lean_inc(v_fvarId_1452_);
lean_dec(v_c_1243_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1497_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1454_, v_a_1244_);
lean_dec(v_y_1454_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v_id_1461_; lean_object* v___x_1462_; 
v_id_1461_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_id_1461_);
lean_dec_ref(v_a_1460_);
v___x_1462_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1452_, v_a_1244_);
lean_dec(v_fvarId_1452_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
if (lean_obj_tag(v_a_1463_) == 0)
{
lean_object* v_id_1464_; lean_object* v___x_1465_; 
v_id_1464_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_id_1464_);
lean_dec_ref(v_a_1463_);
v___x_1465_ = l_Lean_IR_ToIR_lowerCode(v_k_1455_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1476_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 4);
lean_ctor_set(v___x_1457_, 3, v_a_1466_);
lean_ctor_set(v___x_1457_, 2, v_id_1461_);
lean_ctor_set(v___x_1457_, 0, v_id_1464_);
v___x_1471_ = v___x_1457_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_id_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_i_1453_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_id_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_dec(v_id_1464_);
lean_dec(v_id_1461_);
lean_del_object(v___x_1457_);
lean_dec(v_i_1453_);
return v___x_1465_;
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v_a_1463_);
lean_dec(v_id_1461_);
lean_del_object(v___x_1457_);
lean_dec_ref(v_k_1455_);
lean_dec(v_i_1453_);
v___x_1477_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1478_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1477_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1478_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_id_1461_);
lean_del_object(v___x_1457_);
lean_dec_ref(v_k_1455_);
lean_dec(v_i_1453_);
v_a_1479_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1462_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1462_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v_a_1460_);
lean_del_object(v___x_1457_);
lean_dec_ref(v_k_1455_);
lean_dec(v_i_1453_);
lean_dec(v_fvarId_1452_);
v___x_1487_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1488_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1487_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1488_;
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_del_object(v___x_1457_);
lean_dec_ref(v_k_1455_);
lean_dec(v_i_1453_);
lean_dec(v_fvarId_1452_);
v_a_1489_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1459_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1459_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1498_; lean_object* v_i_1499_; lean_object* v_offset_1500_; lean_object* v_y_1501_; lean_object* v_ty_1502_; lean_object* v_k_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1546_; 
v_fvarId_1498_ = lean_ctor_get(v_c_1243_, 0);
v_i_1499_ = lean_ctor_get(v_c_1243_, 1);
v_offset_1500_ = lean_ctor_get(v_c_1243_, 2);
v_y_1501_ = lean_ctor_get(v_c_1243_, 3);
v_ty_1502_ = lean_ctor_get(v_c_1243_, 4);
v_k_1503_ = lean_ctor_get(v_c_1243_, 5);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1505_ = v_c_1243_;
v_isShared_1506_ = v_isSharedCheck_1546_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_k_1503_);
lean_inc(v_ty_1502_);
lean_inc(v_y_1501_);
lean_inc(v_offset_1500_);
lean_inc(v_i_1499_);
lean_inc(v_fvarId_1498_);
lean_dec(v_c_1243_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1546_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1501_, v_a_1244_);
lean_dec(v_y_1501_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
if (lean_obj_tag(v_a_1508_) == 0)
{
lean_object* v_id_1509_; lean_object* v___x_1510_; 
v_id_1509_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_id_1509_);
lean_dec_ref(v_a_1508_);
v___x_1510_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1498_, v_a_1244_);
lean_dec(v_fvarId_1498_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1510_);
if (lean_obj_tag(v_a_1511_) == 0)
{
lean_object* v_id_1512_; lean_object* v___x_1513_; 
v_id_1512_ = lean_ctor_get(v_a_1511_, 0);
lean_inc(v_id_1512_);
lean_dec_ref(v_a_1511_);
v___x_1513_ = l_Lean_IR_ToIR_lowerCode(v_k_1503_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1525_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1525_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1525_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = l_Lean_IR_toIRType(v_ty_1502_);
lean_dec_ref(v_ty_1502_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 5);
lean_ctor_set(v___x_1505_, 5, v_a_1514_);
lean_ctor_set(v___x_1505_, 4, v___x_1518_);
lean_ctor_set(v___x_1505_, 3, v_id_1509_);
lean_ctor_set(v___x_1505_, 0, v_id_1512_);
v___x_1520_ = v___x_1505_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_id_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_i_1499_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_offset_1500_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_id_1509_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v_a_1514_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1520_);
v___x_1522_ = v___x_1516_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_dec(v_id_1512_);
lean_dec(v_id_1509_);
lean_del_object(v___x_1505_);
lean_dec_ref(v_ty_1502_);
lean_dec(v_offset_1500_);
lean_dec(v_i_1499_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1511_);
lean_dec(v_id_1509_);
lean_del_object(v___x_1505_);
lean_dec_ref(v_k_1503_);
lean_dec_ref(v_ty_1502_);
lean_dec(v_offset_1500_);
lean_dec(v_i_1499_);
v___x_1526_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1527_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1526_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1527_;
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_id_1509_);
lean_del_object(v___x_1505_);
lean_dec_ref(v_k_1503_);
lean_dec_ref(v_ty_1502_);
lean_dec(v_offset_1500_);
lean_dec(v_i_1499_);
v_a_1528_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1510_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1510_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_a_1508_);
lean_del_object(v___x_1505_);
lean_dec_ref(v_k_1503_);
lean_dec_ref(v_ty_1502_);
lean_dec(v_offset_1500_);
lean_dec(v_i_1499_);
lean_dec(v_fvarId_1498_);
v___x_1536_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1537_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1536_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1537_;
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1505_);
lean_dec_ref(v_k_1503_);
lean_dec_ref(v_ty_1502_);
lean_dec(v_offset_1500_);
lean_dec(v_i_1499_);
lean_dec(v_fvarId_1498_);
v_a_1538_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1507_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1507_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1547_; lean_object* v_cidx_1548_; lean_object* v_k_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1578_; 
v_fvarId_1547_ = lean_ctor_get(v_c_1243_, 0);
v_cidx_1548_ = lean_ctor_get(v_c_1243_, 1);
v_k_1549_ = lean_ctor_get(v_c_1243_, 2);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1551_ = v_c_1243_;
v_isShared_1552_ = v_isSharedCheck_1578_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_k_1549_);
lean_inc(v_cidx_1548_);
lean_inc(v_fvarId_1547_);
lean_dec(v_c_1243_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1578_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1547_, v_a_1244_);
lean_dec(v_fvarId_1547_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v_a_1554_) == 0)
{
lean_object* v_id_1555_; lean_object* v___x_1556_; 
v_id_1555_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_id_1555_);
lean_dec_ref(v_a_1554_);
v___x_1556_ = l_Lean_IR_ToIR_lowerCode(v_k_1549_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1567_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 3);
lean_ctor_set(v___x_1551_, 2, v_a_1557_);
lean_ctor_set(v___x_1551_, 0, v_id_1555_);
v___x_1562_ = v___x_1551_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_id_1555_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_cidx_1548_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1562_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_dec(v_id_1555_);
lean_del_object(v___x_1551_);
lean_dec(v_cidx_1548_);
return v___x_1556_;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec(v_a_1554_);
lean_del_object(v___x_1551_);
lean_dec_ref(v_k_1549_);
lean_dec(v_cidx_1548_);
v___x_1568_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1569_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1568_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1569_;
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_del_object(v___x_1551_);
lean_dec_ref(v_k_1549_);
lean_dec(v_cidx_1548_);
v_a_1570_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1553_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1553_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1579_; lean_object* v_n_1580_; uint8_t v_check_1581_; uint8_t v_persistent_1582_; lean_object* v_k_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1612_; 
v_fvarId_1579_ = lean_ctor_get(v_c_1243_, 0);
v_n_1580_ = lean_ctor_get(v_c_1243_, 1);
v_check_1581_ = lean_ctor_get_uint8(v_c_1243_, sizeof(void*)*3);
v_persistent_1582_ = lean_ctor_get_uint8(v_c_1243_, sizeof(void*)*3 + 1);
v_k_1583_ = lean_ctor_get(v_c_1243_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1585_ = v_c_1243_;
v_isShared_1586_ = v_isSharedCheck_1612_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_k_1583_);
lean_inc(v_n_1580_);
lean_inc(v_fvarId_1579_);
lean_dec(v_c_1243_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1612_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1579_, v_a_1244_);
lean_dec(v_fvarId_1579_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
if (lean_obj_tag(v_a_1588_) == 0)
{
lean_object* v_id_1589_; lean_object* v___x_1590_; 
v_id_1589_ = lean_ctor_get(v_a_1588_, 0);
lean_inc(v_id_1589_);
lean_dec_ref(v_a_1588_);
v___x_1590_ = l_Lean_IR_ToIR_lowerCode(v_k_1583_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1601_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 6);
lean_ctor_set(v___x_1585_, 2, v_a_1591_);
lean_ctor_set(v___x_1585_, 0, v_id_1589_);
v___x_1596_ = v___x_1585_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_id_1589_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_n_1580_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_a_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1600_, sizeof(void*)*3, v_check_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1600_, sizeof(void*)*3 + 1, v_persistent_1582_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_dec(v_id_1589_);
lean_del_object(v___x_1585_);
lean_dec(v_n_1580_);
return v___x_1590_;
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_a_1588_);
lean_del_object(v___x_1585_);
lean_dec_ref(v_k_1583_);
lean_dec(v_n_1580_);
v___x_1602_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1603_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1602_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1603_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_del_object(v___x_1585_);
lean_dec_ref(v_k_1583_);
lean_dec(v_n_1580_);
v_a_1604_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1587_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1587_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1613_; lean_object* v_n_1614_; uint8_t v_check_1615_; uint8_t v_persistent_1616_; lean_object* v_k_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1646_; 
v_fvarId_1613_ = lean_ctor_get(v_c_1243_, 0);
v_n_1614_ = lean_ctor_get(v_c_1243_, 1);
v_check_1615_ = lean_ctor_get_uint8(v_c_1243_, sizeof(void*)*3);
v_persistent_1616_ = lean_ctor_get_uint8(v_c_1243_, sizeof(void*)*3 + 1);
v_k_1617_ = lean_ctor_get(v_c_1243_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1619_ = v_c_1243_;
v_isShared_1620_ = v_isSharedCheck_1646_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_k_1617_);
lean_inc(v_n_1614_);
lean_inc(v_fvarId_1613_);
lean_dec(v_c_1243_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1646_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1613_, v_a_1244_);
lean_dec(v_fvarId_1613_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
if (lean_obj_tag(v_a_1622_) == 0)
{
lean_object* v_id_1623_; lean_object* v___x_1624_; 
v_id_1623_ = lean_ctor_get(v_a_1622_, 0);
lean_inc(v_id_1623_);
lean_dec_ref(v_a_1622_);
v___x_1624_ = l_Lean_IR_ToIR_lowerCode(v_k_1617_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1635_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 7);
lean_ctor_set(v___x_1619_, 2, v_a_1625_);
lean_ctor_set(v___x_1619_, 0, v_id_1623_);
v___x_1630_ = v___x_1619_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_id_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_n_1614_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_a_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*3, v_check_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*3 + 1, v_persistent_1616_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1630_);
v___x_1632_ = v___x_1627_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_dec(v_id_1623_);
lean_del_object(v___x_1619_);
lean_dec(v_n_1614_);
return v___x_1624_;
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_a_1622_);
lean_del_object(v___x_1619_);
lean_dec_ref(v_k_1617_);
lean_dec(v_n_1614_);
v___x_1636_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1637_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1636_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1637_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_del_object(v___x_1619_);
lean_dec_ref(v_k_1617_);
lean_dec(v_n_1614_);
v_a_1638_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1621_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1621_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
default: 
{
lean_object* v_fvarId_1647_; lean_object* v_k_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1677_; 
v_fvarId_1647_ = lean_ctor_get(v_c_1243_, 0);
v_k_1648_ = lean_ctor_get(v_c_1243_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_c_1243_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1650_ = v_c_1243_;
v_isShared_1651_ = v_isSharedCheck_1677_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_k_1648_);
lean_inc(v_fvarId_1647_);
lean_dec(v_c_1243_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1677_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1647_, v_a_1244_);
lean_dec(v_fvarId_1647_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
if (lean_obj_tag(v_a_1653_) == 0)
{
lean_object* v_id_1654_; lean_object* v___x_1655_; 
v_id_1654_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_id_1654_);
lean_dec_ref(v_a_1653_);
v___x_1655_ = l_Lean_IR_ToIR_lowerCode(v_k_1648_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1666_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1666_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1666_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 8);
lean_ctor_set(v___x_1650_, 1, v_a_1656_);
lean_ctor_set(v___x_1650_, 0, v_id_1654_);
v___x_1661_ = v___x_1650_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_id_1654_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_dec(v_id_1654_);
lean_del_object(v___x_1650_);
return v___x_1655_;
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v_a_1653_);
lean_del_object(v___x_1650_);
lean_dec_ref(v_k_1648_);
v___x_1667_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1668_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1667_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1668_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1650_);
lean_dec_ref(v_k_1648_);
v_a_1669_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1652_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1652_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1678_, lean_object* v_k_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_fvarId_1684_; lean_object* v___x_1685_; 
v_fvarId_1684_ = lean_ctor_get(v_decl_1678_, 0);
lean_inc(v_fvarId_1684_);
lean_dec_ref(v_decl_1678_);
v___x_1685_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1684_, v_a_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref(v___x_1685_);
v___x_1686_ = l_Lean_IR_ToIR_lowerCode(v_k_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
return v___x_1686_;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_k_1679_);
v_a_1687_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1685_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1685_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1695_, lean_object* v_k_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1695_, v_k_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1702_, lean_object* v_k_1703_, lean_object* v_fvarId_1704_, lean_object* v_f_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1702_, v_k_1703_, v_fvarId_1704_, v_f_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec(v_fvarId_1704_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_bs_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_IR_ToIR_lowerAlt(v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1727_, lean_object* v_k_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_IR_ToIR_lowerLet(v_decl_1727_, v_k_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_IR_ToIR_lowerCode(v_c_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1740_, lean_object* v_k_1741_, lean_object* v_x_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1740_, v_k_1741_, v_a_1743_, v_a_1744_, v_a_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1748_, lean_object* v_k_1749_, lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1748_, v_k_1749_, v_x_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_bs_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1756_, v_i_1757_, v_bs_1758_, v___y_1759_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1764_, lean_object* v_i_1765_, lean_object* v_bs_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
size_t v_sz_boxed_1771_; size_t v_i_boxed_1772_; lean_object* v_res_1773_; 
v_sz_boxed_1771_ = lean_unbox_usize(v_sz_1764_);
lean_dec(v_sz_1764_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1771_, v_i_boxed_1772_, v_bs_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1774_, size_t v_i_1775_, lean_object* v_bs_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1774_, v_i_1775_, v_bs_1776_, v___y_1777_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1782_, lean_object* v_i_1783_, lean_object* v_bs_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1782_);
lean_dec(v_sz_1782_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1783_);
lean_dec(v_i_1783_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1789_, v_i_boxed_1790_, v_bs_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_toSignature_1797_; lean_object* v_value_1798_; lean_object* v_name_1799_; lean_object* v_type_1800_; lean_object* v_params_1801_; size_t v_sz_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v_toSignature_1797_ = lean_ctor_get(v_d_1792_, 0);
lean_inc_ref(v_toSignature_1797_);
v_value_1798_ = lean_ctor_get(v_d_1792_, 1);
lean_inc_ref(v_value_1798_);
lean_dec_ref(v_d_1792_);
v_name_1799_ = lean_ctor_get(v_toSignature_1797_, 0);
lean_inc(v_name_1799_);
v_type_1800_ = lean_ctor_get(v_toSignature_1797_, 2);
lean_inc_ref(v_type_1800_);
v_params_1801_ = lean_ctor_get(v_toSignature_1797_, 3);
lean_inc_ref(v_params_1801_);
lean_dec_ref(v_toSignature_1797_);
v_sz_1802_ = lean_array_size(v_params_1801_);
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1802_, v___x_1803_, v_params_1801_, v_a_1793_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1861_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1861_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1861_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_IR_toIRType(v_type_1800_);
lean_dec_ref(v_type_1800_);
if (lean_obj_tag(v_value_1798_) == 0)
{
lean_object* v_code_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1807_);
v_code_1810_ = lean_ctor_get(v_value_1798_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_value_1798_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1812_ = v_value_1798_;
v_isShared_1813_ = v_isSharedCheck_1836_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_code_1810_);
lean_dec(v_value_1798_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1836_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_IR_ToIR_lowerCode(v_code_1810_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1827_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1827_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1827_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1820_, 0, v_name_1799_);
lean_ctor_set(v___x_1820_, 1, v_a_1805_);
lean_ctor_set(v___x_1820_, 2, v___x_1809_);
lean_ctor_set(v___x_1820_, 3, v_a_1815_);
lean_ctor_set(v___x_1820_, 4, v___x_1819_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set_tag(v___x_1812_, 1);
lean_ctor_set(v___x_1812_, 0, v___x_1820_);
v___x_1822_ = v___x_1812_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1822_);
v___x_1824_ = v___x_1817_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_del_object(v___x_1812_);
lean_dec(v___x_1809_);
lean_dec(v_a_1805_);
lean_dec(v_name_1799_);
v_a_1828_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1814_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1814_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1860_; 
v_externAttrData_1837_ = lean_ctor_get(v_value_1798_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_value_1798_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1839_ = v_value_1798_;
v_isShared_1840_ = v_isSharedCheck_1860_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_externAttrData_1837_);
lean_dec(v_value_1798_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1860_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
uint8_t v___x_1841_; 
v___x_1841_ = l_List_isEmpty___redArg(v_externAttrData_1837_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1842_, 0, v_name_1799_);
lean_ctor_set(v___x_1842_, 1, v_a_1805_);
lean_ctor_set(v___x_1842_, 2, v___x_1809_);
lean_ctor_set(v___x_1842_, 3, v_externAttrData_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1842_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1844_);
v___x_1846_ = v___x_1807_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1858_; 
lean_del_object(v___x_1839_);
lean_dec(v_externAttrData_1837_);
lean_del_object(v___x_1807_);
v___x_1849_ = l_Lean_IR_mkDummyExternDecl(v_name_1799_, v_a_1805_, v___x_1809_);
v___x_1850_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1849_, v_a_1795_);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1859_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_box(0);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_type_1800_);
lean_dec(v_name_1799_);
lean_dec_ref(v_value_1798_);
v_a_1862_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1804_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1804_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_IR_ToIR_lowerDecl(v_d_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1876_, size_t v_sz_1877_, size_t v_i_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_b_1879_);
return v___x_1884_;
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_a_1885_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
lean_inc(v_a_1885_);
v___x_1886_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1886_, 0, v_a_1885_);
v___x_1887_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1886_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v_a_1890_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
if (lean_obj_tag(v_a_1888_) == 1)
{
lean_object* v_val_1894_; lean_object* v___x_1895_; 
v_val_1894_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_val_1894_);
lean_dec_ref(v_a_1888_);
v___x_1895_ = lean_array_push(v_b_1879_, v_val_1894_);
v_a_1890_ = v___x_1895_;
goto v___jp_1889_;
}
else
{
lean_dec(v_a_1888_);
v_a_1890_ = v_b_1879_;
goto v___jp_1889_;
}
v___jp_1889_:
{
size_t v___x_1891_; size_t v___x_1892_; 
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_add(v_i_1878_, v___x_1891_);
v_i_1878_ = v___x_1892_;
v_b_1879_ = v_a_1890_;
goto _start;
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref(v_b_1879_);
v_a_1896_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1887_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1887_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1904_, lean_object* v_sz_1905_, lean_object* v_i_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
size_t v_sz_boxed_1911_; size_t v_i_boxed_1912_; lean_object* v_res_1913_; 
v_sz_boxed_1911_ = lean_unbox_usize(v_sz_1905_);
lean_dec(v_sz_1905_);
v_i_boxed_1912_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1904_, v_sz_boxed_1911_, v_i_boxed_1912_, v_b_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec_ref(v_as_1904_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_irDecls_1920_; size_t v_sz_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v_irDecls_1920_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1921_ = lean_array_size(v_decls_1916_);
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1916_, v_sz_1921_, v___x_1922_, v_irDecls_1920_, v_a_1917_, v_a_1918_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_IR_toIR(v_decls_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec_ref(v_decls_1924_);
return v_res_1928_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_ToIR(builtin);
}
#ifdef __cplusplus
}
#endif
