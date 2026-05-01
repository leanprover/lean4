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
lean_object* v___x_412_; lean_object* v_env_413_; lean_object* v_nextMacroScope_414_; lean_object* v_ngen_415_; lean_object* v_auxDeclNGen_416_; lean_object* v_traceState_417_; lean_object* v_messages_418_; lean_object* v_infoState_419_; lean_object* v_snapshotTasks_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_436_; 
v___x_412_ = lean_st_ref_take(v_a_410_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
v_nextMacroScope_414_ = lean_ctor_get(v___x_412_, 1);
v_ngen_415_ = lean_ctor_get(v___x_412_, 2);
v_auxDeclNGen_416_ = lean_ctor_get(v___x_412_, 3);
v_traceState_417_ = lean_ctor_get(v___x_412_, 4);
v_messages_418_ = lean_ctor_get(v___x_412_, 6);
v_infoState_419_ = lean_ctor_get(v___x_412_, 7);
v_snapshotTasks_420_ = lean_ctor_get(v___x_412_, 8);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v___x_412_, 5);
lean_dec(v_unused_437_);
v___x_422_ = v___x_412_;
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_snapshotTasks_420_);
lean_inc(v_infoState_419_);
lean_inc(v_messages_418_);
lean_inc(v_traceState_417_);
lean_inc(v_auxDeclNGen_416_);
lean_inc(v_ngen_415_);
lean_inc(v_nextMacroScope_414_);
lean_inc(v_env_413_);
lean_dec(v___x_412_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_toEnvExtension_425_; lean_object* v_asyncMode_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_424_ = l_Lean_IR_declMapExt;
v_toEnvExtension_425_ = lean_ctor_get(v___x_424_, 0);
v_asyncMode_426_ = lean_ctor_get(v_toEnvExtension_425_, 2);
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_424_, v_env_413_, v_d_409_, v_asyncMode_426_, v___x_427_);
v___x_429_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 5, v___x_429_);
lean_ctor_set(v___x_422_, 0, v___x_428_);
v___x_431_ = v___x_422_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_nextMacroScope_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_ngen_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_auxDeclNGen_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_traceState_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_messages_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_infoState_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_snapshotTasks_420_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_st_ref_set(v_a_410_, v___x_431_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_438_, v_a_439_);
lean_dec(v_a_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_442_, v_a_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_IR_ToIR_addDecl(v_d_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_454_){
_start:
{
switch(lean_obj_tag(v_v_454_))
{
case 0:
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_469_; 
v_val_455_ = lean_ctor_get(v_v_454_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_469_ == 0)
{
v___x_457_ = v_v_454_;
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_v_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___y_460_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_cstr_to_nat("4294967296");
v___x_466_ = lean_nat_dec_lt(v_val_455_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(8);
v___y_460_ = v___x_467_;
goto v___jp_459_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(12);
v___y_460_ = v___x_468_;
goto v___jp_459_;
}
v___jp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_458_ == 0)
{
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_val_455_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; 
lean_inc(v___y_460_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___y_460_);
return v___x_463_;
}
}
}
}
case 1:
{
lean_object* v_val_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_val_470_ = lean_ctor_get(v_v_454_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v_v_454_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_val_470_);
lean_dec(v_v_454_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_val_470_);
v___x_475_ = v_reuseFailAlloc_478_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_box(7);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
}
}
case 2:
{
uint8_t v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_480_ = lean_ctor_get_uint8(v_v_454_, 0);
lean_dec_ref(v_v_454_);
v___x_481_ = lean_uint8_to_nat(v_val_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = lean_box(1);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
return v___x_484_;
}
case 3:
{
uint16_t v_val_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_val_485_ = lean_ctor_get_uint16(v_v_454_, 0);
lean_dec_ref(v_v_454_);
v___x_486_ = lean_uint16_to_nat(v_val_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = lean_box(2);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
case 4:
{
uint32_t v_val_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_val_490_ = lean_ctor_get_uint32(v_v_454_, 0);
lean_dec_ref(v_v_454_);
v___x_491_ = lean_uint32_to_nat(v_val_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
v___x_493_ = lean_box(3);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
return v___x_494_;
}
case 5:
{
uint64_t v_val_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_val_495_ = lean_ctor_get_uint64(v_v_454_, 0);
lean_dec_ref(v_v_454_);
v___x_496_ = lean_uint64_to_nat(v_val_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
v___x_498_ = lean_box(4);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
default: 
{
uint64_t v_val_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_val_500_ = lean_ctor_get_uint64(v_v_454_, 0);
lean_dec_ref(v_v_454_);
v___x_501_ = lean_uint64_to_nat(v_val_500_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = lean_box(5);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_box(1);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_fvarId_510_; lean_object* v___x_511_; 
v_fvarId_510_ = lean_ctor_get(v_a_505_, 0);
v___x_511_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_510_, v_a_506_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec(v_a_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_516_, v_a_517_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_IR_ToIR_lowerArg(v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec(v_a_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_fvarId_531_; lean_object* v_type_532_; uint8_t v_borrow_533_; lean_object* v___x_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
v_fvarId_531_ = lean_ctor_get(v_p_528_, 0);
lean_inc(v_fvarId_531_);
v_type_532_ = lean_ctor_get(v_p_528_, 2);
lean_inc_ref(v_type_532_);
v_borrow_533_ = lean_ctor_get_uint8(v_p_528_, sizeof(void*)*3);
lean_dec_ref(v_p_528_);
v___x_534_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_531_, v_a_529_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_539_ = l_Lean_IR_toIRType(v_type_532_);
lean_dec_ref(v_type_532_);
v___x_540_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_540_, 0, v_a_535_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*2, v_borrow_533_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_545_, v_a_546_);
lean_dec(v_a_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_549_, v_a_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_IR_ToIR_lowerParam(v_p_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_561_){
_start:
{
lean_object* v_name_562_; lean_object* v_cidx_563_; lean_object* v_size_564_; lean_object* v_usize_565_; lean_object* v_ssize_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_name_562_ = lean_ctor_get(v_i_561_, 0);
v_cidx_563_ = lean_ctor_get(v_i_561_, 1);
v_size_564_ = lean_ctor_get(v_i_561_, 2);
v_usize_565_ = lean_ctor_get(v_i_561_, 3);
v_ssize_566_ = lean_ctor_get(v_i_561_, 4);
v_isSharedCheck_573_ = !lean_is_exclusive(v_i_561_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v_i_561_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_ssize_566_);
lean_inc(v_usize_565_);
lean_inc(v_size_564_);
lean_inc(v_cidx_563_);
lean_inc(v_name_562_);
lean_dec(v_i_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_name_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_cidx_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_size_564_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_usize_565_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_ssize_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_instMonadEIO(lean_box(0));
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_toApplicative_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_616_; 
v___x_582_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_583_ = l_StateRefT_x27_instMonad___redArg(v___x_582_);
v_toApplicative_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_583_, 1);
lean_dec(v_unused_617_);
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_616_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_toApplicative_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_616_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_toFunctor_588_; lean_object* v_toSeq_589_; lean_object* v_toSeqLeft_590_; lean_object* v_toSeqRight_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_toFunctor_588_ = lean_ctor_get(v_toApplicative_584_, 0);
v_toSeq_589_ = lean_ctor_get(v_toApplicative_584_, 2);
v_toSeqLeft_590_ = lean_ctor_get(v_toApplicative_584_, 3);
v_toSeqRight_591_ = lean_ctor_get(v_toApplicative_584_, 4);
v_isSharedCheck_614_ = !lean_is_exclusive(v_toApplicative_584_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_toApplicative_584_, 1);
lean_dec(v_unused_615_);
v___x_593_ = v_toApplicative_584_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_toSeqRight_591_);
lean_inc(v_toSeqLeft_590_);
lean_inc(v_toSeq_589_);
lean_inc(v_toFunctor_588_);
lean_dec(v_toApplicative_584_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_604_; 
v___f_595_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_596_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_588_);
v___f_597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_597_, 0, v_toFunctor_588_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_598_, 0, v_toFunctor_588_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___f_597_);
lean_ctor_set(v___x_599_, 1, v___f_598_);
v___f_600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_600_, 0, v_toSeqRight_591_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeqLeft_590_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_602_, 0, v_toSeq_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v___f_600_);
lean_ctor_set(v___x_593_, 3, v___f_601_);
lean_ctor_set(v___x_593_, 2, v___f_602_);
lean_ctor_set(v___x_593_, 1, v___f_595_);
lean_ctor_set(v___x_593_, 0, v___x_599_);
v___x_604_ = v___x_593_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___f_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v___f_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___f_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___f_600_);
v___x_604_ = v_reuseFailAlloc_613_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___f_596_);
lean_ctor_set(v___x_586_, 0, v___x_604_);
v___x_606_ = v___x_586_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___f_596_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_8612__overap_610_; lean_object* v___x_611_; 
v___x_607_ = l_StateRefT_x27_instMonad___redArg(v___x_606_);
v___x_608_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_609_ = l_instInhabitedOfMonad___redArg(v___x_607_, v___x_608_);
v___x_8612__overap_610_ = lean_panic_fn_borrowed(v___x_609_, v_msg_577_);
lean_dec(v___x_609_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_578_);
v___x_611_ = lean_apply_4(v___x_8612__overap_610_, v___y_578_, v___y_579_, v___y_580_, lean_box(0));
return v___x_611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_624_, size_t v_i_625_, lean_object* v_bs_626_, lean_object* v___y_627_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = lean_usize_dec_lt(v_i_625_, v_sz_624_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_bs_626_);
return v___x_630_;
}
else
{
lean_object* v_v_631_; lean_object* v___x_632_; 
v_v_631_ = lean_array_uget_borrowed(v_bs_626_, v_i_625_);
v___x_632_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_631_, v___y_627_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v_bs_x27_635_; size_t v___x_636_; size_t v___x_637_; lean_object* v___x_638_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = lean_unsigned_to_nat(0u);
v_bs_x27_635_ = lean_array_uset(v_bs_626_, v_i_625_, v___x_634_);
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_add(v_i_625_, v___x_636_);
v___x_638_ = lean_array_uset(v_bs_x27_635_, v_i_625_, v_a_633_);
v_i_625_ = v___x_637_;
v_bs_626_ = v___x_638_;
goto _start;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_bs_626_);
v_a_640_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_632_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_632_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_bs_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
size_t v_sz_boxed_653_; size_t v_i_boxed_654_; lean_object* v_res_655_; 
v_sz_boxed_653_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_654_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_653_, v_i_boxed_654_, v_bs_650_, v___y_651_);
lean_dec(v___y_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_656_, size_t v_i_657_, lean_object* v_bs_658_, lean_object* v___y_659_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_lt(v_i_657_, v_sz_656_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_bs_658_);
return v___x_662_;
}
else
{
lean_object* v_v_663_; lean_object* v___x_664_; 
v_v_663_ = lean_array_uget_borrowed(v_bs_658_, v_i_657_);
lean_inc(v_v_663_);
v___x_664_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_663_, v___y_659_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v_bs_x27_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
v_bs_x27_667_ = lean_array_uset(v_bs_658_, v_i_657_, v___x_666_);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_657_, v___x_668_);
v___x_670_ = lean_array_uset(v_bs_x27_667_, v_i_657_, v_a_665_);
v_i_657_ = v___x_669_;
v_bs_658_ = v___x_670_;
goto _start;
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_bs_658_);
v_a_672_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_664_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_664_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_bs_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_686_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_685_, v_i_boxed_686_, v_bs_682_, v___y_683_);
lean_dec(v___y_683_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_688_, lean_object* v_continueLet_689_, lean_object* v_var_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_695_, 0, v_i_688_);
lean_ctor_set(v___x_695_, 1, v_var_690_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
v___x_696_ = lean_apply_5(v_continueLet_689_, v___x_695_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_697_, lean_object* v_continueLet_698_, lean_object* v_var_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_697_, v_continueLet_698_, v_var_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_705_, lean_object* v_offset_706_, lean_object* v_continueLet_707_, lean_object* v_var_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_713_, 0, v_n_705_);
lean_ctor_set(v___x_713_, 1, v_offset_706_);
lean_ctor_set(v___x_713_, 2, v_var_708_);
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc(v___y_709_);
v___x_714_ = lean_apply_5(v_continueLet_707_, v___x_713_, v___y_709_, v___y_710_, v___y_711_, lean_box(0));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_715_, lean_object* v_offset_716_, lean_object* v_continueLet_717_, lean_object* v_var_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_715_, v_offset_716_, v_continueLet_717_, v_var_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_724_, lean_object* v_continueLet_725_, lean_object* v_var_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v_n_724_);
lean_ctor_set(v___x_731_, 1, v_var_726_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
v___x_732_ = lean_apply_5(v_continueLet_725_, v___x_731_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_733_, lean_object* v_continueLet_734_, lean_object* v_var_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_733_, v_continueLet_734_, v_var_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_741_, lean_object* v_var_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_747_, 0, v_var_742_);
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_743_);
v___x_748_ = lean_apply_5(v_continueLet_741_, v___x_747_, v___y_743_, v___y_744_, v___y_745_, lean_box(0));
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_749_, lean_object* v_var_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_749_, v_var_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_756_, lean_object* v_continueLet_757_, lean_object* v_var_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_763_, 0, v_i_756_);
lean_ctor_set(v___x_763_, 1, v_var_758_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
v___x_764_ = lean_apply_5(v_continueLet_757_, v___x_763_, v___y_759_, v___y_760_, v___y_761_, lean_box(0));
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_765_, lean_object* v_continueLet_766_, lean_object* v_var_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_765_, v_continueLet_766_, v_var_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_773_, lean_object* v_continueLet_774_, lean_object* v_var_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = l_Lean_IR_toIRType(v_ty_773_);
v___x_781_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_var_775_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_776_);
v___x_782_ = lean_apply_5(v_continueLet_774_, v___x_781_, v___y_776_, v___y_777_, v___y_778_, lean_box(0));
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_783_, lean_object* v_continueLet_784_, lean_object* v_var_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_783_, v_continueLet_784_, v_var_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v_ty_783_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_791_, lean_object* v_i_792_, uint8_t v_updateHeader_793_, lean_object* v_continueLet_794_, lean_object* v_var_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_sz_800_ = lean_array_size(v_args_791_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_800_, v___x_801_, v_args_791_, v___y_796_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_name_804_; lean_object* v_cidx_805_; lean_object* v_size_806_; lean_object* v_usize_807_; lean_object* v_ssize_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_817_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
v_name_804_ = lean_ctor_get(v_i_792_, 0);
v_cidx_805_ = lean_ctor_get(v_i_792_, 1);
v_size_806_ = lean_ctor_get(v_i_792_, 2);
v_usize_807_ = lean_ctor_get(v_i_792_, 3);
v_ssize_808_ = lean_ctor_get(v_i_792_, 4);
v_isSharedCheck_817_ = !lean_is_exclusive(v_i_792_);
if (v_isSharedCheck_817_ == 0)
{
v___x_810_ = v_i_792_;
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_ssize_808_);
lean_inc(v_usize_807_);
lean_inc(v_size_806_);
lean_inc(v_cidx_805_);
lean_inc(v_name_804_);
lean_dec(v_i_792_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_name_804_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_cidx_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_size_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_usize_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_ssize_808_);
v___x_813_ = v_reuseFailAlloc_816_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_814_, 0, v_var_795_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
lean_ctor_set(v___x_814_, 2, v_a_803_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*3, v_updateHeader_793_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_796_);
v___x_815_ = lean_apply_5(v_continueLet_794_, v___x_814_, v___y_796_, v___y_797_, v___y_798_, lean_box(0));
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_var_795_);
lean_dec_ref(v_continueLet_794_);
lean_dec_ref(v_i_792_);
v_a_818_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_802_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_802_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_826_, lean_object* v_i_827_, lean_object* v_updateHeader_828_, lean_object* v_continueLet_829_, lean_object* v_var_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v_updateHeader_9654__boxed_835_; lean_object* v_res_836_; 
v_updateHeader_9654__boxed_835_ = lean_unbox(v_updateHeader_828_);
v_res_836_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_826_, v_i_827_, v_updateHeader_9654__boxed_835_, v_continueLet_829_, v_var_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_837_, lean_object* v_var_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_843_, 0, v_var_838_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v___y_839_);
v___x_844_ = lean_apply_5(v_continueLet_837_, v___x_843_, v___y_839_, v___y_840_, v___y_841_, lean_box(0));
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_845_, lean_object* v_var_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_845_, v_var_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_852_, lean_object* v_continueLet_853_, lean_object* v_id_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; 
v_sz_859_ = lean_array_size(v_args_852_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_859_, v___x_860_, v_args_852_, v___y_855_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___x_863_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_863_, 0, v_id_854_);
lean_ctor_set(v___x_863_, 1, v_a_862_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
v___x_864_ = lean_apply_5(v_continueLet_853_, v___x_863_, v___y_855_, v___y_856_, v___y_857_, lean_box(0));
return v___x_864_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_id_854_);
lean_dec_ref(v_continueLet_853_);
v_a_865_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_861_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_861_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_873_, lean_object* v_continueLet_874_, lean_object* v_id_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_873_, v_continueLet_874_, v_id_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_881_, lean_object* v_k_882_, lean_object* v_type_883_, lean_object* v_e_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_881_, v___y_885_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
v___x_891_ = l_Lean_IR_ToIR_lowerCode(v_k_882_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_900_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_896_, 0, v_a_890_);
lean_ctor_set(v___x_896_, 1, v_type_883_);
lean_ctor_set(v___x_896_, 2, v_e_884_);
lean_ctor_set(v___x_896_, 3, v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
lean_dec(v_a_890_);
lean_dec_ref(v_e_884_);
lean_dec(v_type_883_);
return v___x_891_;
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_e_884_);
lean_dec(v_type_883_);
lean_dec_ref(v_k_882_);
v_a_901_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_889_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_889_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_909_, lean_object* v_k_910_, lean_object* v_type_911_, lean_object* v_e_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_909_, v_k_910_, v_type_911_, v_e_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_918_, lean_object* v_k_919_, lean_object* v_fvarId_920_, lean_object* v_f_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_920_, v_a_922_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
if (lean_obj_tag(v_a_927_) == 0)
{
lean_object* v_id_928_; lean_object* v___x_929_; 
lean_dec_ref(v_k_919_);
lean_dec_ref(v_decl_918_);
v_id_928_ = lean_ctor_get(v_a_927_, 0);
lean_inc(v_id_928_);
lean_dec_ref(v_a_927_);
lean_inc(v_a_924_);
lean_inc_ref(v_a_923_);
lean_inc(v_a_922_);
v___x_929_ = lean_apply_5(v_f_921_, v_id_928_, v_a_922_, v_a_923_, v_a_924_, lean_box(0));
return v___x_929_;
}
else
{
lean_object* v___x_930_; 
lean_dec_ref(v_f_921_);
v___x_930_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_918_, v_k_919_, v_a_922_, v_a_923_, v_a_924_);
return v___x_930_;
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v_f_921_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_decl_918_);
v_a_931_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_926_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_926_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_939_, lean_object* v_k_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_fvarId_945_; lean_object* v_type_946_; lean_object* v_value_947_; lean_object* v_type_948_; lean_object* v_continueLet_949_; 
v_fvarId_945_ = lean_ctor_get(v_decl_939_, 0);
v_type_946_ = lean_ctor_get(v_decl_939_, 2);
v_value_947_ = lean_ctor_get(v_decl_939_, 3);
lean_inc(v_value_947_);
v_type_948_ = l_Lean_IR_toIRType(v_type_946_);
lean_inc(v_type_948_);
lean_inc_ref(v_k_940_);
lean_inc(v_fvarId_945_);
v_continueLet_949_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_949_, 0, v_fvarId_945_);
lean_closure_set(v_continueLet_949_, 1, v_k_940_);
lean_closure_set(v_continueLet_949_, 2, v_type_948_);
switch(lean_obj_tag(v_value_947_))
{
case 0:
{
lean_object* v_value_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_960_; 
lean_inc(v_fvarId_945_);
lean_dec_ref(v_continueLet_949_);
lean_dec_ref(v_decl_939_);
v_value_950_ = lean_ctor_get(v_value_947_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_value_947_);
if (v_isSharedCheck_960_ == 0)
{
v___x_952_ = v_value_947_;
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_value_950_);
lean_dec(v_value_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v_fst_955_; lean_object* v___x_957_; 
v___x_954_ = l_Lean_IR_ToIR_lowerLitValue(v_value_950_);
v_fst_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_fst_955_);
lean_dec_ref(v___x_954_);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 11);
lean_ctor_set(v___x_952_, 0, v_fst_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_955_);
v___x_957_ = v_reuseFailAlloc_959_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_945_, v_k_940_, v_type_948_, v___x_957_, v_a_941_, v_a_942_, v_a_943_);
return v___x_958_;
}
}
}
case 1:
{
lean_object* v___x_961_; 
lean_dec_ref(v_continueLet_949_);
lean_dec(v_type_948_);
v___x_961_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_939_, v_k_940_, v_a_941_, v_a_942_, v_a_943_);
return v___x_961_;
}
case 4:
{
lean_object* v_fvarId_962_; lean_object* v_args_963_; lean_object* v___f_964_; lean_object* v___x_965_; 
lean_dec(v_type_948_);
v_fvarId_962_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_fvarId_962_);
v_args_963_ = lean_ctor_get(v_value_947_, 1);
lean_inc_ref(v_args_963_);
lean_dec_ref(v_value_947_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_964_, 0, v_args_963_);
lean_closure_set(v___f_964_, 1, v_continueLet_949_);
v___x_965_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_fvarId_962_, v___f_964_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_fvarId_962_);
return v___x_965_;
}
case 5:
{
lean_object* v_i_966_; lean_object* v_args_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_999_; 
lean_inc(v_fvarId_945_);
lean_dec_ref(v_continueLet_949_);
lean_dec_ref(v_decl_939_);
v_i_966_ = lean_ctor_get(v_value_947_, 0);
v_args_967_ = lean_ctor_get(v_value_947_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_value_947_);
if (v_isSharedCheck_999_ == 0)
{
v___x_969_ = v_value_947_;
v_isShared_970_ = v_isSharedCheck_999_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_args_967_);
lean_inc(v_i_966_);
lean_dec(v_value_947_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_999_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
size_t v_sz_971_; size_t v___x_972_; lean_object* v___x_973_; 
v_sz_971_ = lean_array_size(v_args_967_);
v___x_972_ = ((size_t)0ULL);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_971_, v___x_972_, v_args_967_, v_a_941_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v_name_975_; lean_object* v_cidx_976_; lean_object* v_size_977_; lean_object* v_usize_978_; lean_object* v_ssize_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v_name_975_ = lean_ctor_get(v_i_966_, 0);
v_cidx_976_ = lean_ctor_get(v_i_966_, 1);
v_size_977_ = lean_ctor_get(v_i_966_, 2);
v_usize_978_ = lean_ctor_get(v_i_966_, 3);
v_ssize_979_ = lean_ctor_get(v_i_966_, 4);
v_isSharedCheck_990_ = !lean_is_exclusive(v_i_966_);
if (v_isSharedCheck_990_ == 0)
{
v___x_981_ = v_i_966_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_ssize_979_);
lean_inc(v_usize_978_);
lean_inc(v_size_977_);
lean_inc(v_cidx_976_);
lean_inc(v_name_975_);
lean_dec(v_i_966_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_name_975_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_cidx_976_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_size_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_usize_978_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_ssize_979_);
v___x_984_ = v_reuseFailAlloc_989_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 0);
lean_ctor_set(v___x_969_, 1, v_a_974_);
lean_ctor_set(v___x_969_, 0, v___x_984_);
v___x_986_ = v___x_969_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_a_974_);
v___x_986_ = v_reuseFailAlloc_988_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_945_, v_k_940_, v_type_948_, v___x_986_, v_a_941_, v_a_942_, v_a_943_);
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_969_);
lean_dec_ref(v_i_966_);
lean_dec(v_type_948_);
lean_dec(v_fvarId_945_);
lean_dec_ref(v_k_940_);
v_a_991_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_973_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_973_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1000_; lean_object* v_var_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; 
lean_dec(v_type_948_);
v_i_1000_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_i_1000_);
v_var_1001_ = lean_ctor_get(v_value_947_, 1);
lean_inc(v_var_1001_);
lean_dec_ref(v_value_947_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1002_, 0, v_i_1000_);
lean_closure_set(v___f_1002_, 1, v_continueLet_949_);
v___x_1003_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_var_1001_, v___f_1002_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_var_1001_);
return v___x_1003_;
}
case 7:
{
lean_object* v_i_1004_; lean_object* v_var_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; 
lean_dec(v_type_948_);
v_i_1004_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_i_1004_);
v_var_1005_ = lean_ctor_get(v_value_947_, 1);
lean_inc(v_var_1005_);
lean_dec_ref(v_value_947_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1006_, 0, v_i_1004_);
lean_closure_set(v___f_1006_, 1, v_continueLet_949_);
v___x_1007_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_var_1005_, v___f_1006_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_var_1005_);
return v___x_1007_;
}
case 8:
{
lean_object* v_n_1008_; lean_object* v_offset_1009_; lean_object* v_var_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
lean_dec(v_type_948_);
v_n_1008_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_n_1008_);
v_offset_1009_ = lean_ctor_get(v_value_947_, 1);
lean_inc(v_offset_1009_);
v_var_1010_ = lean_ctor_get(v_value_947_, 2);
lean_inc(v_var_1010_);
lean_dec_ref(v_value_947_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1011_, 0, v_n_1008_);
lean_closure_set(v___f_1011_, 1, v_offset_1009_);
lean_closure_set(v___f_1011_, 2, v_continueLet_949_);
v___x_1012_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_var_1010_, v___f_1011_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_var_1010_);
return v___x_1012_;
}
case 9:
{
lean_object* v_fn_1013_; lean_object* v_args_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1034_; 
lean_inc(v_fvarId_945_);
lean_dec_ref(v_continueLet_949_);
lean_dec_ref(v_decl_939_);
v_fn_1013_ = lean_ctor_get(v_value_947_, 0);
v_args_1014_ = lean_ctor_get(v_value_947_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_value_947_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1016_ = v_value_947_;
v_isShared_1017_ = v_isSharedCheck_1034_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_args_1014_);
lean_inc(v_fn_1013_);
lean_dec(v_value_947_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1034_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
size_t v_sz_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v_sz_1018_ = lean_array_size(v_args_1014_);
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1018_, v___x_1019_, v_args_1014_, v_a_941_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 6);
lean_ctor_set(v___x_1016_, 1, v_a_1021_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_fn_1013_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_a_1021_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_945_, v_k_940_, v_type_948_, v___x_1023_, v_a_941_, v_a_942_, v_a_943_);
return v___x_1024_;
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_del_object(v___x_1016_);
lean_dec(v_fn_1013_);
lean_dec(v_type_948_);
lean_dec(v_fvarId_945_);
lean_dec_ref(v_k_940_);
v_a_1026_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1020_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1020_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1035_; lean_object* v_args_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1056_; 
lean_inc(v_fvarId_945_);
lean_dec_ref(v_continueLet_949_);
lean_dec_ref(v_decl_939_);
v_fn_1035_ = lean_ctor_get(v_value_947_, 0);
v_args_1036_ = lean_ctor_get(v_value_947_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_value_947_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1038_ = v_value_947_;
v_isShared_1039_ = v_isSharedCheck_1056_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_args_1036_);
lean_inc(v_fn_1035_);
lean_dec(v_value_947_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1056_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v_sz_1040_ = lean_array_size(v_args_1036_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1040_, v___x_1041_, v_args_1036_, v_a_941_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1042_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 7);
lean_ctor_set(v___x_1038_, 1, v_a_1043_);
v___x_1045_ = v___x_1038_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fn_1035_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_a_1043_);
v___x_1045_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_945_, v_k_940_, v_type_948_, v___x_1045_, v_a_941_, v_a_942_, v_a_943_);
return v___x_1046_;
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_del_object(v___x_1038_);
lean_dec(v_fn_1035_);
lean_dec(v_type_948_);
lean_dec(v_fvarId_945_);
lean_dec_ref(v_k_940_);
v_a_1048_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1042_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1042_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1057_; lean_object* v_var_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
lean_dec(v_type_948_);
v_n_1057_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_n_1057_);
v_var_1058_ = lean_ctor_get(v_value_947_, 1);
lean_inc(v_var_1058_);
lean_dec_ref(v_value_947_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1059_, 0, v_n_1057_);
lean_closure_set(v___f_1059_, 1, v_continueLet_949_);
v___x_1060_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_var_1058_, v___f_1059_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_var_1058_);
return v___x_1060_;
}
case 12:
{
lean_object* v_var_1061_; lean_object* v_i_1062_; uint8_t v_updateHeader_1063_; lean_object* v_args_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; 
lean_dec(v_type_948_);
v_var_1061_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_var_1061_);
v_i_1062_ = lean_ctor_get(v_value_947_, 1);
lean_inc_ref(v_i_1062_);
v_updateHeader_1063_ = lean_ctor_get_uint8(v_value_947_, sizeof(void*)*3);
v_args_1064_ = lean_ctor_get(v_value_947_, 2);
lean_inc_ref(v_args_1064_);
lean_dec_ref(v_value_947_);
v___x_1065_ = lean_box(v_updateHeader_1063_);
v___f_1066_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1066_, 0, v_args_1064_);
lean_closure_set(v___f_1066_, 1, v_i_1062_);
lean_closure_set(v___f_1066_, 2, v___x_1065_);
lean_closure_set(v___f_1066_, 3, v_continueLet_949_);
v___x_1067_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_var_1061_, v___f_1066_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_var_1061_);
return v___x_1067_;
}
case 13:
{
lean_object* v_ty_1068_; lean_object* v_fvarId_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
lean_dec(v_type_948_);
v_ty_1068_ = lean_ctor_get(v_value_947_, 0);
lean_inc_ref(v_ty_1068_);
v_fvarId_1069_ = lean_ctor_get(v_value_947_, 1);
lean_inc(v_fvarId_1069_);
lean_dec_ref(v_value_947_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1070_, 0, v_ty_1068_);
lean_closure_set(v___f_1070_, 1, v_continueLet_949_);
v___x_1071_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_fvarId_1069_, v___f_1070_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_fvarId_1069_);
return v___x_1071_;
}
case 14:
{
lean_object* v_fvarId_1072_; lean_object* v___f_1073_; lean_object* v___x_1074_; 
lean_dec(v_type_948_);
v_fvarId_1072_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_fvarId_1072_);
lean_dec_ref(v_value_947_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1073_, 0, v_continueLet_949_);
v___x_1074_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_fvarId_1072_, v___f_1073_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_fvarId_1072_);
return v___x_1074_;
}
default: 
{
lean_object* v_fvarId_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
lean_dec(v_type_948_);
v_fvarId_1075_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_fvarId_1075_);
lean_dec_ref(v_value_947_);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1076_, 0, v_continueLet_949_);
v___x_1077_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_939_, v_k_940_, v_fvarId_1075_, v___f_1076_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_fvarId_1075_);
return v___x_1077_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1081_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1082_ = lean_unsigned_to_nat(15u);
v___x_1083_ = lean_unsigned_to_nat(128u);
v___x_1084_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1085_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1086_ = l_mkPanicMessageWithDecl(v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_, v___x_1081_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
if (lean_obj_tag(v_a_1087_) == 1)
{
lean_object* v_info_1092_; lean_object* v_code_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1129_; 
v_info_1092_ = lean_ctor_get(v_a_1087_, 0);
v_code_1093_ = lean_ctor_get(v_a_1087_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1095_ = v_a_1087_;
v_isShared_1096_ = v_isSharedCheck_1129_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_code_1093_);
lean_inc(v_info_1092_);
lean_dec(v_a_1087_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1129_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_IR_ToIR_lowerCode(v_code_1093_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1120_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1120_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1120_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_name_1102_; lean_object* v_cidx_1103_; lean_object* v_size_1104_; lean_object* v_usize_1105_; lean_object* v_ssize_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1119_; 
v_name_1102_ = lean_ctor_get(v_info_1092_, 0);
v_cidx_1103_ = lean_ctor_get(v_info_1092_, 1);
v_size_1104_ = lean_ctor_get(v_info_1092_, 2);
v_usize_1105_ = lean_ctor_get(v_info_1092_, 3);
v_ssize_1106_ = lean_ctor_get(v_info_1092_, 4);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_info_1092_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1108_ = v_info_1092_;
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_ssize_1106_);
lean_inc(v_usize_1105_);
lean_inc(v_size_1104_);
lean_inc(v_cidx_1103_);
lean_inc(v_name_1102_);
lean_dec(v_info_1092_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_name_1102_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_cidx_1103_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_size_1104_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_usize_1105_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v_ssize_1106_);
v___x_1111_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 1, v_a_1098_);
lean_ctor_set(v___x_1095_, 0, v___x_1111_);
v___x_1113_ = v___x_1095_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_a_1098_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1113_);
v___x_1115_ = v___x_1100_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_del_object(v___x_1095_);
lean_dec_ref(v_info_1092_);
v_a_1121_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1097_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1097_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
else
{
lean_object* v_code_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1154_; 
v_code_1130_ = lean_ctor_get(v_a_1087_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1132_ = v_a_1087_;
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_code_1130_);
lean_dec(v_a_1087_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_IR_ToIR_lowerCode(v_code_1130_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1145_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1145_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1145_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 1);
lean_ctor_set(v___x_1132_, 0, v_a_1135_);
v___x_1140_ = v___x_1132_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1140_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_del_object(v___x_1132_);
v_a_1146_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1134_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1134_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_bs_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_bs_1157_);
return v___x_1163_;
}
else
{
lean_object* v_v_1164_; lean_object* v___x_1165_; 
v_v_1164_ = lean_array_uget_borrowed(v_bs_1157_, v_i_1156_);
lean_inc(v_v_1164_);
v___x_1165_ = l_Lean_IR_ToIR_lowerAlt(v_v_1164_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v_bs_x27_1168_; size_t v___x_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v_bs_x27_1168_ = lean_array_uset(v_bs_1157_, v_i_1156_, v___x_1167_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1156_, v___x_1169_);
v___x_1171_ = lean_array_uset(v_bs_x27_1168_, v_i_1156_, v_a_1166_);
v_i_1156_ = v___x_1170_;
v_bs_1157_ = v___x_1171_;
goto _start;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_bs_1157_);
v_a_1173_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1165_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1165_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1182_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1183_ = lean_unsigned_to_nat(53u);
v___x_1184_ = lean_unsigned_to_nat(95u);
v___x_1185_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1186_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1187_ = l_mkPanicMessageWithDecl(v___x_1186_, v___x_1185_, v___x_1184_, v___x_1183_, v___x_1182_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1189_ = lean_unsigned_to_nat(44u);
v___x_1190_ = lean_unsigned_to_nat(106u);
v___x_1191_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1192_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1193_ = l_mkPanicMessageWithDecl(v___x_1192_, v___x_1191_, v___x_1190_, v___x_1189_, v___x_1188_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1195_ = lean_unsigned_to_nat(44u);
v___x_1196_ = lean_unsigned_to_nat(114u);
v___x_1197_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1198_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1199_ = l_mkPanicMessageWithDecl(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1201_ = lean_unsigned_to_nat(34u);
v___x_1202_ = lean_unsigned_to_nat(113u);
v___x_1203_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1204_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1205_ = l_mkPanicMessageWithDecl(v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1207_ = lean_unsigned_to_nat(44u);
v___x_1208_ = lean_unsigned_to_nat(110u);
v___x_1209_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1210_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1211_ = l_mkPanicMessageWithDecl(v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1213_ = lean_unsigned_to_nat(34u);
v___x_1214_ = lean_unsigned_to_nat(109u);
v___x_1215_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1216_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1217_ = l_mkPanicMessageWithDecl(v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1218_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1219_ = lean_unsigned_to_nat(41u);
v___x_1220_ = lean_unsigned_to_nat(117u);
v___x_1221_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1223_ = l_mkPanicMessageWithDecl(v___x_1222_, v___x_1221_, v___x_1220_, v___x_1219_, v___x_1218_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1225_ = lean_unsigned_to_nat(41u);
v___x_1226_ = lean_unsigned_to_nat(120u);
v___x_1227_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1228_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1229_ = l_mkPanicMessageWithDecl(v___x_1228_, v___x_1227_, v___x_1226_, v___x_1225_, v___x_1224_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1231_ = lean_unsigned_to_nat(41u);
v___x_1232_ = lean_unsigned_to_nat(123u);
v___x_1233_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1234_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1235_ = l_mkPanicMessageWithDecl(v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_, v___x_1230_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1237_ = lean_unsigned_to_nat(41u);
v___x_1238_ = lean_unsigned_to_nat(126u);
v___x_1239_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1240_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1241_ = l_mkPanicMessageWithDecl(v___x_1240_, v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
switch(lean_obj_tag(v_c_1242_))
{
case 0:
{
lean_object* v_decl_1247_; lean_object* v_k_1248_; lean_object* v___x_1249_; 
v_decl_1247_ = lean_ctor_get(v_c_1242_, 0);
lean_inc_ref(v_decl_1247_);
v_k_1248_ = lean_ctor_get(v_c_1242_, 1);
lean_inc_ref(v_k_1248_);
lean_dec_ref(v_c_1242_);
v___x_1249_ = l_Lean_IR_ToIR_lowerLet(v_decl_1247_, v_k_1248_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1249_;
}
case 1:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v_c_1242_);
v___x_1250_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1251_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1250_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1251_;
}
case 2:
{
lean_object* v_decl_1252_; lean_object* v_k_1253_; lean_object* v_fvarId_1254_; lean_object* v_params_1255_; lean_object* v_value_1256_; lean_object* v___x_1257_; 
v_decl_1252_ = lean_ctor_get(v_c_1242_, 0);
lean_inc_ref(v_decl_1252_);
v_k_1253_ = lean_ctor_get(v_c_1242_, 1);
lean_inc_ref(v_k_1253_);
lean_dec_ref(v_c_1242_);
v_fvarId_1254_ = lean_ctor_get(v_decl_1252_, 0);
lean_inc(v_fvarId_1254_);
v_params_1255_ = lean_ctor_get(v_decl_1252_, 2);
lean_inc_ref(v_params_1255_);
v_value_1256_ = lean_ctor_get(v_decl_1252_, 4);
lean_inc_ref(v_value_1256_);
lean_dec_ref(v_decl_1252_);
v___x_1257_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1254_, v_a_1243_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; size_t v_sz_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v_sz_1259_ = lean_array_size(v_params_1255_);
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1259_, v___x_1260_, v_params_1255_, v_a_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = l_Lean_IR_ToIR_lowerCode(v_value_1256_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = l_Lean_IR_ToIR_lowerCode(v_k_1253_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1274_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1258_);
lean_ctor_set(v___x_1270_, 1, v_a_1262_);
lean_ctor_set(v___x_1270_, 2, v_a_1264_);
lean_ctor_set(v___x_1270_, 3, v_a_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_dec(v_a_1264_);
lean_dec(v_a_1262_);
lean_dec(v_a_1258_);
return v___x_1265_;
}
}
else
{
lean_dec(v_a_1262_);
lean_dec(v_a_1258_);
lean_dec_ref(v_k_1253_);
return v___x_1263_;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_a_1258_);
lean_dec_ref(v_value_1256_);
lean_dec_ref(v_k_1253_);
v_a_1275_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1261_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1261_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_value_1256_);
lean_dec_ref(v_params_1255_);
lean_dec_ref(v_k_1253_);
v_a_1283_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1257_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1257_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1291_; lean_object* v_args_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1328_; 
v_fvarId_1291_ = lean_ctor_get(v_c_1242_, 0);
v_args_1292_ = lean_ctor_get(v_c_1242_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1294_ = v_c_1242_;
v_isShared_1295_ = v_isSharedCheck_1328_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_args_1292_);
lean_inc(v_fvarId_1291_);
lean_dec(v_c_1242_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1328_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1291_, v_a_1243_);
lean_dec(v_fvarId_1291_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; size_t v_sz_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1296_);
v_sz_1298_ = lean_array_size(v_args_1292_);
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1298_, v___x_1299_, v_args_1292_, v_a_1243_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1311_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1311_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1311_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 11);
lean_ctor_set(v___x_1294_, 1, v_a_1301_);
lean_ctor_set(v___x_1294_, 0, v_a_1297_);
v___x_1306_ = v___x_1294_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1297_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1306_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1297_);
lean_del_object(v___x_1294_);
v_a_1312_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1300_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1300_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_del_object(v___x_1294_);
lean_dec_ref(v_args_1292_);
v_a_1320_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1296_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1296_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1329_; lean_object* v_typeName_1330_; lean_object* v_discr_1331_; lean_object* v_alts_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1372_; 
v_cases_1329_ = lean_ctor_get(v_c_1242_, 0);
lean_inc_ref(v_cases_1329_);
lean_dec_ref(v_c_1242_);
v_typeName_1330_ = lean_ctor_get(v_cases_1329_, 0);
v_discr_1331_ = lean_ctor_get(v_cases_1329_, 2);
v_alts_1332_ = lean_ctor_get(v_cases_1329_, 3);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_cases_1329_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v_cases_1329_, 1);
lean_dec(v_unused_1373_);
v___x_1334_ = v_cases_1329_;
v_isShared_1335_ = v_isSharedCheck_1372_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_alts_1332_);
lean_inc(v_discr_1331_);
lean_inc(v_typeName_1330_);
lean_dec(v_cases_1329_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1372_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1331_, v_a_1243_);
lean_dec(v_discr_1331_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1336_);
if (lean_obj_tag(v_a_1337_) == 0)
{
lean_object* v_id_1338_; size_t v_sz_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
v_id_1338_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_id_1338_);
lean_dec_ref(v_a_1337_);
v_sz_1339_ = lean_array_size(v_alts_1332_);
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1339_, v___x_1340_, v_alts_1332_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1353_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1353_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1353_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = l_Lean_IR_nameToIRType(v_typeName_1330_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 9);
lean_ctor_set(v___x_1334_, 3, v_a_1342_);
lean_ctor_set(v___x_1334_, 2, v___x_1346_);
lean_ctor_set(v___x_1334_, 1, v_id_1338_);
v___x_1348_ = v___x_1334_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_typeName_1330_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_id_1338_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_a_1342_);
v___x_1348_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1348_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_id_1338_);
lean_del_object(v___x_1334_);
lean_dec(v_typeName_1330_);
v_a_1354_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1341_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1341_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_a_1337_);
lean_del_object(v___x_1334_);
lean_dec_ref(v_alts_1332_);
lean_dec(v_typeName_1330_);
v___x_1362_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1363_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1362_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1363_;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_del_object(v___x_1334_);
lean_dec_ref(v_alts_1332_);
lean_dec(v_typeName_1330_);
v_a_1364_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1336_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1336_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1398_; 
v_fvarId_1374_ = lean_ctor_get(v_c_1242_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1376_ = v_c_1242_;
v_isShared_1377_ = v_isSharedCheck_1398_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_fvarId_1374_);
lean_dec(v_c_1242_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1398_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1374_, v_a_1243_);
lean_dec(v_fvarId_1374_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1389_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1389_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1389_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 10);
lean_ctor_set(v___x_1376_, 0, v_a_1379_);
v___x_1384_ = v___x_1376_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_del_object(v___x_1376_);
v_a_1390_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1378_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1378_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_c_1242_, 0);
lean_dec(v_unused_1407_);
v___x_1400_ = v_c_1242_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_c_1242_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(12);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
case 7:
{
lean_object* v_fvarId_1408_; lean_object* v_i_1409_; lean_object* v_y_1410_; lean_object* v_k_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1450_; 
v_fvarId_1408_ = lean_ctor_get(v_c_1242_, 0);
v_i_1409_ = lean_ctor_get(v_c_1242_, 1);
v_y_1410_ = lean_ctor_get(v_c_1242_, 2);
v_k_1411_ = lean_ctor_get(v_c_1242_, 3);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1413_ = v_c_1242_;
v_isShared_1414_ = v_isSharedCheck_1450_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_k_1411_);
lean_inc(v_y_1410_);
lean_inc(v_i_1409_);
lean_inc(v_fvarId_1408_);
lean_dec(v_c_1242_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1450_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1410_, v_a_1243_);
lean_dec(v_y_1410_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1408_, v_a_1243_);
lean_dec(v_fvarId_1408_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
if (lean_obj_tag(v_a_1418_) == 0)
{
lean_object* v_id_1419_; lean_object* v___x_1420_; 
v_id_1419_ = lean_ctor_get(v_a_1418_, 0);
lean_inc(v_id_1419_);
lean_dec_ref(v_a_1418_);
v___x_1420_ = l_Lean_IR_ToIR_lowerCode(v_k_1411_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1431_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1431_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1431_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 2);
lean_ctor_set(v___x_1413_, 3, v_a_1421_);
lean_ctor_set(v___x_1413_, 2, v_a_1416_);
lean_ctor_set(v___x_1413_, 0, v_id_1419_);
v___x_1426_ = v___x_1413_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_id_1419_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_i_1409_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_a_1416_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1426_);
v___x_1428_ = v___x_1423_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_dec(v_id_1419_);
lean_dec(v_a_1416_);
lean_del_object(v___x_1413_);
lean_dec(v_i_1409_);
return v___x_1420_;
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_a_1418_);
lean_dec(v_a_1416_);
lean_del_object(v___x_1413_);
lean_dec_ref(v_k_1411_);
lean_dec(v_i_1409_);
v___x_1432_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1433_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1432_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1433_;
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1416_);
lean_del_object(v___x_1413_);
lean_dec_ref(v_k_1411_);
lean_dec(v_i_1409_);
v_a_1434_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1417_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1417_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1413_);
lean_dec_ref(v_k_1411_);
lean_dec(v_i_1409_);
lean_dec(v_fvarId_1408_);
v_a_1442_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1415_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1415_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1451_; lean_object* v_i_1452_; lean_object* v_y_1453_; lean_object* v_k_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1496_; 
v_fvarId_1451_ = lean_ctor_get(v_c_1242_, 0);
v_i_1452_ = lean_ctor_get(v_c_1242_, 1);
v_y_1453_ = lean_ctor_get(v_c_1242_, 2);
v_k_1454_ = lean_ctor_get(v_c_1242_, 3);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1456_ = v_c_1242_;
v_isShared_1457_ = v_isSharedCheck_1496_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_k_1454_);
lean_inc(v_y_1453_);
lean_inc(v_i_1452_);
lean_inc(v_fvarId_1451_);
lean_dec(v_c_1242_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1496_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1453_, v_a_1243_);
lean_dec(v_y_1453_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
if (lean_obj_tag(v_a_1459_) == 0)
{
lean_object* v_id_1460_; lean_object* v___x_1461_; 
v_id_1460_ = lean_ctor_get(v_a_1459_, 0);
lean_inc(v_id_1460_);
lean_dec_ref(v_a_1459_);
v___x_1461_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1451_, v_a_1243_);
lean_dec(v_fvarId_1451_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
if (lean_obj_tag(v_a_1462_) == 0)
{
lean_object* v_id_1463_; lean_object* v___x_1464_; 
v_id_1463_ = lean_ctor_get(v_a_1462_, 0);
lean_inc(v_id_1463_);
lean_dec_ref(v_a_1462_);
v___x_1464_ = l_Lean_IR_ToIR_lowerCode(v_k_1454_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1475_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1475_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1475_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 4);
lean_ctor_set(v___x_1456_, 3, v_a_1465_);
lean_ctor_set(v___x_1456_, 2, v_id_1460_);
lean_ctor_set(v___x_1456_, 0, v_id_1463_);
v___x_1470_ = v___x_1456_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_id_1463_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_i_1452_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_id_1460_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1470_);
v___x_1472_ = v___x_1467_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_dec(v_id_1463_);
lean_dec(v_id_1460_);
lean_del_object(v___x_1456_);
lean_dec(v_i_1452_);
return v___x_1464_;
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v_a_1462_);
lean_dec(v_id_1460_);
lean_del_object(v___x_1456_);
lean_dec_ref(v_k_1454_);
lean_dec(v_i_1452_);
v___x_1476_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1477_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1476_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1477_;
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_id_1460_);
lean_del_object(v___x_1456_);
lean_dec_ref(v_k_1454_);
lean_dec(v_i_1452_);
v_a_1478_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1461_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1461_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v_a_1459_);
lean_del_object(v___x_1456_);
lean_dec_ref(v_k_1454_);
lean_dec(v_i_1452_);
lean_dec(v_fvarId_1451_);
v___x_1486_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1487_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1486_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1487_;
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_del_object(v___x_1456_);
lean_dec_ref(v_k_1454_);
lean_dec(v_i_1452_);
lean_dec(v_fvarId_1451_);
v_a_1488_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1458_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1458_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1497_; lean_object* v_i_1498_; lean_object* v_offset_1499_; lean_object* v_y_1500_; lean_object* v_ty_1501_; lean_object* v_k_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1545_; 
v_fvarId_1497_ = lean_ctor_get(v_c_1242_, 0);
v_i_1498_ = lean_ctor_get(v_c_1242_, 1);
v_offset_1499_ = lean_ctor_get(v_c_1242_, 2);
v_y_1500_ = lean_ctor_get(v_c_1242_, 3);
v_ty_1501_ = lean_ctor_get(v_c_1242_, 4);
v_k_1502_ = lean_ctor_get(v_c_1242_, 5);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1504_ = v_c_1242_;
v_isShared_1505_ = v_isSharedCheck_1545_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_k_1502_);
lean_inc(v_ty_1501_);
lean_inc(v_y_1500_);
lean_inc(v_offset_1499_);
lean_inc(v_i_1498_);
lean_inc(v_fvarId_1497_);
lean_dec(v_c_1242_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1545_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1500_, v_a_1243_);
lean_dec(v_y_1500_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref(v___x_1506_);
if (lean_obj_tag(v_a_1507_) == 0)
{
lean_object* v_id_1508_; lean_object* v___x_1509_; 
v_id_1508_ = lean_ctor_get(v_a_1507_, 0);
lean_inc(v_id_1508_);
lean_dec_ref(v_a_1507_);
v___x_1509_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1497_, v_a_1243_);
lean_dec(v_fvarId_1497_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
if (lean_obj_tag(v_a_1510_) == 0)
{
lean_object* v_id_1511_; lean_object* v___x_1512_; 
v_id_1511_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_id_1511_);
lean_dec_ref(v_a_1510_);
v___x_1512_ = l_Lean_IR_ToIR_lowerCode(v_k_1502_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1524_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1524_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1524_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = l_Lean_IR_toIRType(v_ty_1501_);
lean_dec_ref(v_ty_1501_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 5);
lean_ctor_set(v___x_1504_, 5, v_a_1513_);
lean_ctor_set(v___x_1504_, 4, v___x_1517_);
lean_ctor_set(v___x_1504_, 3, v_id_1508_);
lean_ctor_set(v___x_1504_, 0, v_id_1511_);
v___x_1519_ = v___x_1504_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_id_1511_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_i_1498_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_offset_1499_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_id_1508_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1523_, 5, v_a_1513_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1519_);
v___x_1521_ = v___x_1515_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_dec(v_id_1511_);
lean_dec(v_id_1508_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_ty_1501_);
lean_dec(v_offset_1499_);
lean_dec(v_i_1498_);
return v___x_1512_;
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v_a_1510_);
lean_dec(v_id_1508_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_k_1502_);
lean_dec_ref(v_ty_1501_);
lean_dec(v_offset_1499_);
lean_dec(v_i_1498_);
v___x_1525_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1526_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1525_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1526_;
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_id_1508_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_k_1502_);
lean_dec_ref(v_ty_1501_);
lean_dec(v_offset_1499_);
lean_dec(v_i_1498_);
v_a_1527_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1509_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1509_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_a_1507_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_k_1502_);
lean_dec_ref(v_ty_1501_);
lean_dec(v_offset_1499_);
lean_dec(v_i_1498_);
lean_dec(v_fvarId_1497_);
v___x_1535_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1536_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1535_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1536_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_del_object(v___x_1504_);
lean_dec_ref(v_k_1502_);
lean_dec_ref(v_ty_1501_);
lean_dec(v_offset_1499_);
lean_dec(v_i_1498_);
lean_dec(v_fvarId_1497_);
v_a_1537_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1506_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1506_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1546_; lean_object* v_cidx_1547_; lean_object* v_k_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1577_; 
v_fvarId_1546_ = lean_ctor_get(v_c_1242_, 0);
v_cidx_1547_ = lean_ctor_get(v_c_1242_, 1);
v_k_1548_ = lean_ctor_get(v_c_1242_, 2);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1550_ = v_c_1242_;
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_k_1548_);
lean_inc(v_cidx_1547_);
lean_inc(v_fvarId_1546_);
lean_dec(v_c_1242_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1546_, v_a_1243_);
lean_dec(v_fvarId_1546_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v_a_1553_) == 0)
{
lean_object* v_id_1554_; lean_object* v___x_1555_; 
v_id_1554_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_id_1554_);
lean_dec_ref(v_a_1553_);
v___x_1555_ = l_Lean_IR_ToIR_lowerCode(v_k_1548_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1566_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1566_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1566_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 3);
lean_ctor_set(v___x_1550_, 2, v_a_1556_);
lean_ctor_set(v___x_1550_, 0, v_id_1554_);
v___x_1561_ = v___x_1550_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_id_1554_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_cidx_1547_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1561_);
v___x_1563_ = v___x_1558_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_dec(v_id_1554_);
lean_del_object(v___x_1550_);
lean_dec(v_cidx_1547_);
return v___x_1555_;
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec(v_a_1553_);
lean_del_object(v___x_1550_);
lean_dec_ref(v_k_1548_);
lean_dec(v_cidx_1547_);
v___x_1567_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1568_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1567_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1568_;
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1550_);
lean_dec_ref(v_k_1548_);
lean_dec(v_cidx_1547_);
v_a_1569_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1552_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1552_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1578_; lean_object* v_n_1579_; uint8_t v_check_1580_; uint8_t v_persistent_1581_; lean_object* v_k_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1611_; 
v_fvarId_1578_ = lean_ctor_get(v_c_1242_, 0);
v_n_1579_ = lean_ctor_get(v_c_1242_, 1);
v_check_1580_ = lean_ctor_get_uint8(v_c_1242_, sizeof(void*)*3);
v_persistent_1581_ = lean_ctor_get_uint8(v_c_1242_, sizeof(void*)*3 + 1);
v_k_1582_ = lean_ctor_get(v_c_1242_, 2);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1584_ = v_c_1242_;
v_isShared_1585_ = v_isSharedCheck_1611_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_k_1582_);
lean_inc(v_n_1579_);
lean_inc(v_fvarId_1578_);
lean_dec(v_c_1242_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1611_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1578_, v_a_1243_);
lean_dec(v_fvarId_1578_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
if (lean_obj_tag(v_a_1587_) == 0)
{
lean_object* v_id_1588_; lean_object* v___x_1589_; 
v_id_1588_ = lean_ctor_get(v_a_1587_, 0);
lean_inc(v_id_1588_);
lean_dec_ref(v_a_1587_);
v___x_1589_ = l_Lean_IR_ToIR_lowerCode(v_k_1582_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 6);
lean_ctor_set(v___x_1584_, 2, v_a_1590_);
lean_ctor_set(v___x_1584_, 0, v_id_1588_);
v___x_1595_ = v___x_1584_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_id_1588_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_n_1579_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_a_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*3, v_check_1580_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*3 + 1, v_persistent_1581_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_dec(v_id_1588_);
lean_del_object(v___x_1584_);
lean_dec(v_n_1579_);
return v___x_1589_;
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec(v_a_1587_);
lean_del_object(v___x_1584_);
lean_dec_ref(v_k_1582_);
lean_dec(v_n_1579_);
v___x_1601_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1602_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1601_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1602_;
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1584_);
lean_dec_ref(v_k_1582_);
lean_dec(v_n_1579_);
v_a_1603_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1586_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1586_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1612_; lean_object* v_n_1613_; uint8_t v_check_1614_; uint8_t v_persistent_1615_; lean_object* v_k_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1645_; 
v_fvarId_1612_ = lean_ctor_get(v_c_1242_, 0);
v_n_1613_ = lean_ctor_get(v_c_1242_, 1);
v_check_1614_ = lean_ctor_get_uint8(v_c_1242_, sizeof(void*)*3);
v_persistent_1615_ = lean_ctor_get_uint8(v_c_1242_, sizeof(void*)*3 + 1);
v_k_1616_ = lean_ctor_get(v_c_1242_, 2);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1618_ = v_c_1242_;
v_isShared_1619_ = v_isSharedCheck_1645_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_k_1616_);
lean_inc(v_n_1613_);
lean_inc(v_fvarId_1612_);
lean_dec(v_c_1242_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1645_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1612_, v_a_1243_);
lean_dec(v_fvarId_1612_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
if (lean_obj_tag(v_a_1621_) == 0)
{
lean_object* v_id_1622_; lean_object* v___x_1623_; 
v_id_1622_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_id_1622_);
lean_dec_ref(v_a_1621_);
v___x_1623_ = l_Lean_IR_ToIR_lowerCode(v_k_1616_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1634_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 7);
lean_ctor_set(v___x_1618_, 2, v_a_1624_);
lean_ctor_set(v___x_1618_, 0, v_id_1622_);
v___x_1629_ = v___x_1618_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_id_1622_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_n_1613_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_a_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*3, v_check_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*3 + 1, v_persistent_1615_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_dec(v_id_1622_);
lean_del_object(v___x_1618_);
lean_dec(v_n_1613_);
return v___x_1623_;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_a_1621_);
lean_del_object(v___x_1618_);
lean_dec_ref(v_k_1616_);
lean_dec(v_n_1613_);
v___x_1635_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1636_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1635_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1636_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_del_object(v___x_1618_);
lean_dec_ref(v_k_1616_);
lean_dec(v_n_1613_);
v_a_1637_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1620_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1620_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
default: 
{
lean_object* v_fvarId_1646_; lean_object* v_k_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1676_; 
v_fvarId_1646_ = lean_ctor_get(v_c_1242_, 0);
v_k_1647_ = lean_ctor_get(v_c_1242_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_c_1242_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1649_ = v_c_1242_;
v_isShared_1650_ = v_isSharedCheck_1676_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_k_1647_);
lean_inc(v_fvarId_1646_);
lean_dec(v_c_1242_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1676_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1646_, v_a_1243_);
lean_dec(v_fvarId_1646_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref(v___x_1651_);
if (lean_obj_tag(v_a_1652_) == 0)
{
lean_object* v_id_1653_; lean_object* v___x_1654_; 
v_id_1653_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_id_1653_);
lean_dec_ref(v_a_1652_);
v___x_1654_ = l_Lean_IR_ToIR_lowerCode(v_k_1647_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1665_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 8);
lean_ctor_set(v___x_1649_, 1, v_a_1655_);
lean_ctor_set(v___x_1649_, 0, v_id_1653_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_id_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_dec(v_id_1653_);
lean_del_object(v___x_1649_);
return v___x_1654_;
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_a_1652_);
lean_del_object(v___x_1649_);
lean_dec_ref(v_k_1647_);
v___x_1666_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1667_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1666_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1667_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1649_);
lean_dec_ref(v_k_1647_);
v_a_1668_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1651_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1651_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1677_, lean_object* v_k_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_fvarId_1683_; lean_object* v___x_1684_; 
v_fvarId_1683_ = lean_ctor_get(v_decl_1677_, 0);
lean_inc(v_fvarId_1683_);
lean_dec_ref(v_decl_1677_);
v___x_1684_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1683_, v_a_1679_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref(v___x_1684_);
v___x_1685_ = l_Lean_IR_ToIR_lowerCode(v_k_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_k_1678_);
v_a_1686_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1684_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1694_, lean_object* v_k_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1694_, v_k_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1701_, lean_object* v_k_1702_, lean_object* v_fvarId_1703_, lean_object* v_f_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1701_, v_k_1702_, v_fvarId_1703_, v_f_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec(v_fvarId_1703_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1710_, lean_object* v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1710_);
lean_dec(v_sz_1710_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_IR_ToIR_lowerAlt(v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1726_, lean_object* v_k_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_IR_ToIR_lowerLet(v_decl_1726_, v_k_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_IR_ToIR_lowerCode(v_c_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1739_, lean_object* v_k_1740_, lean_object* v_x_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1739_, v_k_1740_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1747_, lean_object* v_k_1748_, lean_object* v_x_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1747_, v_k_1748_, v_x_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1755_, size_t v_i_1756_, lean_object* v_bs_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1755_, v_i_1756_, v_bs_1757_, v___y_1758_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_bs_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1770_, v_i_boxed_1771_, v_bs_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_bs_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1773_, v_i_1774_, v_bs_1775_, v___y_1776_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_bs_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1788_, v_i_boxed_1789_, v_bs_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_toSignature_1796_; lean_object* v_value_1797_; lean_object* v_name_1798_; lean_object* v_type_1799_; lean_object* v_params_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v_toSignature_1796_ = lean_ctor_get(v_d_1791_, 0);
lean_inc_ref(v_toSignature_1796_);
v_value_1797_ = lean_ctor_get(v_d_1791_, 1);
lean_inc_ref(v_value_1797_);
lean_dec_ref(v_d_1791_);
v_name_1798_ = lean_ctor_get(v_toSignature_1796_, 0);
lean_inc(v_name_1798_);
v_type_1799_ = lean_ctor_get(v_toSignature_1796_, 2);
lean_inc_ref(v_type_1799_);
v_params_1800_ = lean_ctor_get(v_toSignature_1796_, 3);
lean_inc_ref(v_params_1800_);
lean_dec_ref(v_toSignature_1796_);
v_sz_1801_ = lean_array_size(v_params_1800_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1801_, v___x_1802_, v_params_1800_, v_a_1792_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1860_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1860_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1860_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_IR_toIRType(v_type_1799_);
lean_dec_ref(v_type_1799_);
if (lean_obj_tag(v_value_1797_) == 0)
{
lean_object* v_code_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1835_; 
lean_del_object(v___x_1806_);
v_code_1809_ = lean_ctor_get(v_value_1797_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_value_1797_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1811_ = v_value_1797_;
v_isShared_1812_ = v_isSharedCheck_1835_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_code_1809_);
lean_dec(v_value_1797_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1835_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_IR_ToIR_lowerCode(v_code_1809_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1826_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1826_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1826_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1819_, 0, v_name_1798_);
lean_ctor_set(v___x_1819_, 1, v_a_1804_);
lean_ctor_set(v___x_1819_, 2, v___x_1808_);
lean_ctor_set(v___x_1819_, 3, v_a_1814_);
lean_ctor_set(v___x_1819_, 4, v___x_1818_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
lean_ctor_set(v___x_1811_, 0, v___x_1819_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1821_);
v___x_1823_ = v___x_1816_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_del_object(v___x_1811_);
lean_dec(v___x_1808_);
lean_dec(v_a_1804_);
lean_dec(v_name_1798_);
v_a_1827_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1813_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1813_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1859_; 
v_externAttrData_1836_ = lean_ctor_get(v_value_1797_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_value_1797_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1838_ = v_value_1797_;
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_externAttrData_1836_);
lean_dec(v_value_1797_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_List_isEmpty___redArg(v_externAttrData_1836_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1841_, 0, v_name_1798_);
lean_ctor_set(v___x_1841_, 1, v_a_1804_);
lean_ctor_set(v___x_1841_, 2, v___x_1808_);
lean_ctor_set(v___x_1841_, 3, v_externAttrData_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1843_);
v___x_1845_ = v___x_1806_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
lean_del_object(v___x_1838_);
lean_dec(v_externAttrData_1836_);
lean_del_object(v___x_1806_);
v___x_1848_ = l_Lean_IR_mkDummyExternDecl(v_name_1798_, v_a_1804_, v___x_1808_);
v___x_1849_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1848_, v_a_1794_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1858_);
v___x_1851_ = v___x_1849_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v___x_1849_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(0);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_type_1799_);
lean_dec(v_name_1798_);
lean_dec_ref(v_value_1797_);
v_a_1861_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1803_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1803_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_IR_ToIR_lowerDecl(v_d_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1875_, size_t v_sz_1876_, size_t v_i_1877_, lean_object* v_b_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_usize_dec_lt(v_i_1877_, v_sz_1876_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_b_1878_);
return v___x_1883_;
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_a_1884_ = lean_array_uget_borrowed(v_as_1875_, v_i_1877_);
lean_inc(v_a_1884_);
v___x_1885_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1885_, 0, v_a_1884_);
v___x_1886_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1885_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_a_1889_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
if (lean_obj_tag(v_a_1887_) == 1)
{
lean_object* v_val_1893_; lean_object* v___x_1894_; 
v_val_1893_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_val_1893_);
lean_dec_ref(v_a_1887_);
v___x_1894_ = lean_array_push(v_b_1878_, v_val_1893_);
v_a_1889_ = v___x_1894_;
goto v___jp_1888_;
}
else
{
lean_dec(v_a_1887_);
v_a_1889_ = v_b_1878_;
goto v___jp_1888_;
}
v___jp_1888_:
{
size_t v___x_1890_; size_t v___x_1891_; 
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1877_, v___x_1890_);
v_i_1877_ = v___x_1891_;
v_b_1878_ = v_a_1889_;
goto _start;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_b_1878_);
v_a_1895_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1886_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1886_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1903_, lean_object* v_sz_1904_, lean_object* v_i_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
size_t v_sz_boxed_1910_; size_t v_i_boxed_1911_; lean_object* v_res_1912_; 
v_sz_boxed_1910_ = lean_unbox_usize(v_sz_1904_);
lean_dec(v_sz_1904_);
v_i_boxed_1911_ = lean_unbox_usize(v_i_1905_);
lean_dec(v_i_1905_);
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1903_, v_sz_boxed_1910_, v_i_boxed_1911_, v_b_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_as_1903_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_irDecls_1919_; size_t v_sz_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v_irDecls_1919_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1920_ = lean_array_size(v_decls_1915_);
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1915_, v_sz_1920_, v___x_1921_, v_irDecls_1919_, v_a_1916_, v_a_1917_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_IR_toIR(v_decls_1923_, v_a_1924_, v_a_1925_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_decls_1923_);
return v_res_1927_;
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
