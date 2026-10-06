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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_9_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
lean_ctor_set(v___x_9_, 3, v___x_7_);
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
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_nbuckets_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_222_ = lean_array_get_size(v_data_221_);
v___x_223_ = lean_unsigned_to_nat(2u);
v_nbuckets_224_ = lean_nat_mul(v___x_222_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_box(0);
v___x_227_ = lean_mk_array(v_nbuckets_224_, v___x_226_);
v___x_228_ = lean_array_propagate_mark(v_data_221_, v___x_227_);
v___x_229_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v___x_225_, v_data_221_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* v_m_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
lean_object* v_size_233_; lean_object* v_buckets_234_; lean_object* v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v_fold_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; lean_object* v_bkt_248_; uint8_t v___x_249_; 
v_size_233_ = lean_ctor_get(v_m_230_, 0);
v_buckets_234_ = lean_ctor_get(v_m_230_, 1);
v___x_235_ = lean_array_get_size(v_buckets_234_);
v___x_236_ = l_Lean_instHashableFVarId_hash(v_a_231_);
v___x_237_ = 32ULL;
v___x_238_ = lean_uint64_shift_right(v___x_236_, v___x_237_);
v_fold_239_ = lean_uint64_xor(v___x_236_, v___x_238_);
v___x_240_ = 16ULL;
v___x_241_ = lean_uint64_shift_right(v_fold_239_, v___x_240_);
v___x_242_ = lean_uint64_xor(v_fold_239_, v___x_241_);
v___x_243_ = lean_uint64_to_usize(v___x_242_);
v___x_244_ = lean_usize_of_nat(v___x_235_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_sub(v___x_244_, v___x_245_);
v___x_247_ = lean_usize_land(v___x_243_, v___x_246_);
v_bkt_248_ = lean_array_uget_borrowed(v_buckets_234_, v___x_247_);
v___x_249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_231_, v_bkt_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_270_; 
lean_inc_ref(v_buckets_234_);
lean_inc(v_size_233_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_m_230_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_271_ = lean_ctor_get(v_m_230_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_m_230_, 0);
lean_dec(v_unused_272_);
v___x_251_ = v_m_230_;
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_m_230_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v_size_x27_254_; lean_object* v___x_255_; lean_object* v_buckets_x27_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v_size_x27_254_ = lean_nat_add(v_size_233_, v___x_253_);
lean_dec(v_size_233_);
lean_inc(v_bkt_248_);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v_a_231_);
lean_ctor_set(v___x_255_, 1, v_b_232_);
lean_ctor_set(v___x_255_, 2, v_bkt_248_);
v_buckets_x27_256_ = lean_array_uset(v_buckets_234_, v___x_247_, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_mul(v_size_x27_254_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(3u);
v___x_260_ = lean_nat_div(v___x_258_, v___x_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_array_get_size(v_buckets_x27_256_);
v___x_262_ = lean_nat_dec_le(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
if (v___x_262_ == 0)
{
lean_object* v_val_263_; lean_object* v___x_265_; 
v_val_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_buckets_x27_256_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_val_263_);
lean_ctor_set(v___x_251_, 0, v_size_x27_254_);
v___x_265_ = v___x_251_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_size_x27_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_val_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v___x_268_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_buckets_x27_256_);
lean_ctor_set(v___x_251_, 0, v_size_x27_254_);
v___x_268_ = v___x_251_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_x27_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_buckets_x27_256_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_dec(v_b_232_);
lean_dec(v_a_231_);
return v_m_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* v_fvarId_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; lean_object* v_vars_277_; lean_object* v_joinPoints_278_; lean_object* v_nextVarId_279_; lean_object* v_nextJpId_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_293_; 
v___x_276_ = lean_st_ref_take(v_a_274_);
v_vars_277_ = lean_ctor_get(v___x_276_, 0);
v_joinPoints_278_ = lean_ctor_get(v___x_276_, 1);
v_nextVarId_279_ = lean_ctor_get(v___x_276_, 2);
v_nextJpId_280_ = lean_ctor_get(v___x_276_, 3);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_293_ == 0)
{
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_293_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_nextJpId_280_);
lean_inc(v_nextVarId_279_);
lean_inc(v_joinPoints_278_);
lean_inc(v_vars_277_);
lean_dec(v___x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_293_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
lean_inc(v_nextVarId_279_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_nextVarId_279_);
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_277_, v_fvarId_273_, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_nextVarId_279_, v___x_286_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 2, v___x_287_);
lean_ctor_set(v___x_282_, 0, v___x_285_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_joinPoints_278_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_nextJpId_280_);
v___x_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_st_ref_put(v_a_274_, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_nextVarId_279_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_294_, v_a_295_);
lean_dec(v_a_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_298_, v_a_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_IR_ToIR_bindVar(v_fvarId_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_310_, lean_object* v_m_311_, lean_object* v_a_312_, lean_object* v_b_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_311_, v_a_312_, v_b_313_);
return v___x_314_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_x_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_319_, v_a_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* v_00_u03b2_324_, lean_object* v_data_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_327_, lean_object* v_i_328_, lean_object* v_source_329_, lean_object* v_target_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_328_, v_source_329_, v_target_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; lean_object* v_vars_340_; lean_object* v_joinPoints_341_; lean_object* v_nextVarId_342_; lean_object* v_nextJpId_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_355_; 
v___x_339_ = lean_st_ref_take(v_a_337_);
v_vars_340_ = lean_ctor_get(v___x_339_, 0);
v_joinPoints_341_ = lean_ctor_get(v___x_339_, 1);
v_nextVarId_342_ = lean_ctor_get(v___x_339_, 2);
v_nextJpId_343_ = lean_ctor_get(v___x_339_, 3);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_355_ == 0)
{
v___x_345_ = v___x_339_;
v_isShared_346_ = v_isSharedCheck_355_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_nextJpId_343_);
lean_inc(v_nextVarId_342_);
lean_inc(v_joinPoints_341_);
lean_inc(v_vars_340_);
lean_dec(v___x_339_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_355_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc(v_nextJpId_343_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_341_, v_fvarId_336_, v_nextJpId_343_);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_nextJpId_343_, v___x_348_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 3, v___x_349_);
lean_ctor_set(v___x_345_, 1, v___x_347_);
v___x_351_ = v___x_345_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_vars_340_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_nextVarId_342_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v___x_349_);
v___x_351_ = v_reuseFailAlloc_354_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_st_ref_put(v_a_337_, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_nextJpId_343_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_356_, v_a_357_);
lean_dec(v_a_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_360_, v_a_361_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_vars_376_; lean_object* v_joinPoints_377_; lean_object* v_nextVarId_378_; lean_object* v_nextJpId_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_391_; 
v___x_375_ = lean_st_ref_take(v_a_373_);
v_vars_376_ = lean_ctor_get(v___x_375_, 0);
v_joinPoints_377_ = lean_ctor_get(v___x_375_, 1);
v_nextVarId_378_ = lean_ctor_get(v___x_375_, 2);
v_nextJpId_379_ = lean_ctor_get(v___x_375_, 3);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_391_ == 0)
{
v___x_381_ = v___x_375_;
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_nextJpId_379_);
lean_inc(v_nextVarId_378_);
lean_inc(v_joinPoints_377_);
lean_inc(v_vars_376_);
lean_dec(v___x_375_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_box(1);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_376_, v_fvarId_372_, v___x_384_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_387_ = v___x_381_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_joinPoints_377_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_nextVarId_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_nextJpId_379_);
v___x_387_ = v_reuseFailAlloc_390_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_st_ref_put(v_a_373_, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_383_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_392_, v_a_393_);
lean_dec(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_396_, v_a_397_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_IR_ToIR_bindErased(v_fvarId_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___lam__0(lean_object* v___x_408_, lean_object* v_d_409_, lean_object* v_s_410_){
_start:
{
lean_object* v_addEntryFn_411_; lean_object* v_importedEntries_412_; lean_object* v_state_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_addEntryFn_411_ = lean_ctor_get(v___x_408_, 3);
lean_inc(v_addEntryFn_411_);
lean_dec_ref(v___x_408_);
v_importedEntries_412_ = lean_ctor_get(v_s_410_, 0);
v_state_413_ = lean_ctor_get(v_s_410_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_s_410_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_s_410_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_state_413_);
lean_inc(v_importedEntries_412_);
lean_dec(v_s_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_state_417_; lean_object* v___x_419_; 
v_state_417_ = lean_apply_2(v_addEntryFn_411_, v_state_413_, v_d_409_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_state_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_importedEntries_412_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_state_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_422_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_env_431_; lean_object* v_nextMacroScope_432_; lean_object* v_ngen_433_; lean_object* v_auxDeclNGen_434_; lean_object* v_traceState_435_; lean_object* v_recordedDeps_436_; lean_object* v_messages_437_; lean_object* v_infoState_438_; lean_object* v_snapshotTasks_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_462_; 
v___x_430_ = lean_st_ref_take(v_a_428_);
v_env_431_ = lean_ctor_get(v___x_430_, 0);
v_nextMacroScope_432_ = lean_ctor_get(v___x_430_, 1);
v_ngen_433_ = lean_ctor_get(v___x_430_, 2);
v_auxDeclNGen_434_ = lean_ctor_get(v___x_430_, 3);
v_traceState_435_ = lean_ctor_get(v___x_430_, 4);
v_recordedDeps_436_ = lean_ctor_get(v___x_430_, 6);
v_messages_437_ = lean_ctor_get(v___x_430_, 7);
v_infoState_438_ = lean_ctor_get(v___x_430_, 8);
v_snapshotTasks_439_ = lean_ctor_get(v___x_430_, 9);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_430_, 5);
lean_dec(v_unused_463_);
v___x_441_ = v___x_430_;
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snapshotTasks_439_);
lean_inc(v_infoState_438_);
lean_inc(v_messages_437_);
lean_inc(v_recordedDeps_436_);
lean_inc(v_traceState_435_);
lean_inc(v_auxDeclNGen_434_);
lean_inc(v_ngen_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_env_431_);
lean_dec(v___x_430_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v_toEnvExtension_444_; lean_object* v_asyncMode_445_; uint8_t v_logWrites_446_; lean_object* v___x_447_; lean_object* v___y_449_; lean_object* v___f_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_443_ = l_Lean_IR_declMapExt;
v_toEnvExtension_444_ = lean_ctor_get(v___x_443_, 0);
v_asyncMode_445_ = lean_ctor_get(v_toEnvExtension_444_, 2);
v_logWrites_446_ = lean_ctor_get_uint8(v_toEnvExtension_444_, sizeof(void*)*6);
v___x_447_ = lean_box(0);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_addDecl___redArg___lam__0), 3, 2);
lean_closure_set(v___f_456_, 0, v___x_443_);
lean_closure_set(v___f_456_, 1, v_d_427_);
v___x_457_ = lean_box(0);
v___x_458_ = 1;
if (v_logWrites_446_ == 0)
{
lean_object* v___x_459_; 
lean_inc_ref(v_toEnvExtension_444_);
v___x_459_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_444_, v_env_431_, v___f_456_, v_asyncMode_445_, v___x_457_, v___x_458_);
v___y_449_ = v___x_459_;
goto v___jp_448_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc_ref_n(v_toEnvExtension_444_, 2);
v___x_460_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_444_, v_env_431_);
lean_dec_ref(v_env_431_);
v___x_461_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_444_, v___x_460_, v___f_456_, v_asyncMode_445_, v___x_457_, v___x_458_);
v___y_449_ = v___x_461_;
goto v___jp_448_;
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 5, v___x_450_);
lean_ctor_set(v___x_441_, 0, v___y_449_);
v___x_452_ = v___x_441_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___y_449_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_ngen_433_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_auxDeclNGen_434_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_traceState_435_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_recordedDeps_436_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_messages_437_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_infoState_438_);
lean_ctor_set(v_reuseFailAlloc_455_, 9, v_snapshotTasks_439_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_st_ref_put(v_a_428_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_447_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_464_, v_a_465_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_468_, v_a_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_IR_ToIR_addDecl(v_d_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_480_){
_start:
{
switch(lean_obj_tag(v_v_480_))
{
case 0:
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_495_; 
v_val_481_ = lean_ctor_get(v_v_480_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_v_480_);
if (v_isSharedCheck_495_ == 0)
{
v___x_483_ = v_v_480_;
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_v_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___y_486_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_cstr_to_nat("4294967296");
v___x_492_ = lean_nat_dec_lt(v_val_481_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(8);
v___y_486_ = v___x_493_;
goto v___jp_485_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(12);
v___y_486_ = v___x_494_;
goto v___jp_485_;
}
v___jp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_484_ == 0)
{
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_val_481_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
lean_inc(v___y_486_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___y_486_);
return v___x_489_;
}
}
}
}
case 1:
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v_val_496_ = lean_ctor_get(v_v_480_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_v_480_);
if (v_isSharedCheck_505_ == 0)
{
v___x_498_ = v_v_480_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_v_480_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_val_496_);
v___x_501_ = v_reuseFailAlloc_504_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(7);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
}
}
case 2:
{
uint8_t v_val_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_val_506_ = lean_ctor_get_uint8(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_507_ = lean_uint8_to_nat(v_val_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = lean_box(1);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
case 3:
{
uint16_t v_val_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_val_511_ = lean_ctor_get_uint16(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_512_ = lean_uint16_to_nat(v_val_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_box(2);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
case 4:
{
uint32_t v_val_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_val_516_ = lean_ctor_get_uint32(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_517_ = lean_uint32_to_nat(v_val_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___x_519_ = lean_box(3);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
case 5:
{
uint64_t v_val_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_val_521_ = lean_ctor_get_uint64(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_522_ = lean_uint64_to_nat(v_val_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
v___x_524_ = lean_box(4);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
default: 
{
uint64_t v_val_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_val_526_ = lean_ctor_get_uint64(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_527_ = lean_uint64_to_nat(v_val_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_box(5);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
if (lean_obj_tag(v_a_531_) == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_box(1);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
else
{
lean_object* v_fvarId_536_; lean_object* v___x_537_; 
v_fvarId_536_ = lean_ctor_get(v_a_531_, 0);
v___x_537_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_536_, v_a_532_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec(v_a_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_542_, v_a_543_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_IR_ToIR_lowerArg(v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec(v_a_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_fvarId_557_; lean_object* v_type_558_; uint8_t v_borrow_559_; lean_object* v___x_560_; lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_574_; 
v_fvarId_557_ = lean_ctor_get(v_p_554_, 0);
lean_inc(v_fvarId_557_);
v_type_558_ = lean_ctor_get(v_p_554_, 2);
lean_inc_ref(v_type_558_);
v_borrow_559_ = lean_ctor_get_uint8(v_p_554_, sizeof(void*)*3);
lean_dec_ref(v_p_554_);
v___x_560_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_557_, v_a_555_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_574_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_574_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_574_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v___y_567_; 
v___x_565_ = l_Lean_IR_toIRType(v_type_558_);
lean_dec_ref(v_type_558_);
if (v_borrow_559_ == 0)
{
v___y_567_ = v_borrow_559_;
goto v___jp_566_;
}
else
{
uint8_t v___x_572_; 
v___x_572_ = l_Lean_IR_IRType_isScalar(v___x_565_);
if (v___x_572_ == 0)
{
v___y_567_ = v_borrow_559_;
goto v___jp_566_;
}
else
{
uint8_t v___x_573_; 
v___x_573_ = 0;
v___y_567_ = v___x_573_;
goto v___jp_566_;
}
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_568_, 0, v_a_561_);
lean_ctor_set(v___x_568_, 1, v___x_565_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*2, v___y_567_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_568_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_575_, v_a_576_);
lean_dec(v_a_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_579_, v_a_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_IR_ToIR_lowerParam(v_p_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_591_){
_start:
{
lean_object* v_name_592_; lean_object* v_cidx_593_; lean_object* v_size_594_; lean_object* v_usize_595_; lean_object* v_ssize_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_name_592_ = lean_ctor_get(v_i_591_, 0);
v_cidx_593_ = lean_ctor_get(v_i_591_, 1);
v_size_594_ = lean_ctor_get(v_i_591_, 2);
v_usize_595_ = lean_ctor_get(v_i_591_, 3);
v_ssize_596_ = lean_ctor_get(v_i_591_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v_i_591_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v_i_591_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_ssize_596_);
lean_inc(v_usize_595_);
lean_inc(v_size_594_);
lean_inc(v_cidx_593_);
lean_inc(v_name_592_);
lean_dec(v_i_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_name_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_cidx_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_size_594_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_usize_595_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_ssize_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_instMonadEIO___redArg();
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_toApplicative_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_646_; 
v___x_612_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_613_ = l_StateRefT_x27_instMonad___redArg(v___x_612_);
v_toApplicative_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v___x_613_, 1);
lean_dec(v_unused_647_);
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_646_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_toApplicative_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_646_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_toFunctor_618_; lean_object* v_toSeq_619_; lean_object* v_toSeqLeft_620_; lean_object* v_toSeqRight_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_644_; 
v_toFunctor_618_ = lean_ctor_get(v_toApplicative_614_, 0);
v_toSeq_619_ = lean_ctor_get(v_toApplicative_614_, 2);
v_toSeqLeft_620_ = lean_ctor_get(v_toApplicative_614_, 3);
v_toSeqRight_621_ = lean_ctor_get(v_toApplicative_614_, 4);
v_isSharedCheck_644_ = !lean_is_exclusive(v_toApplicative_614_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v_toApplicative_614_, 1);
lean_dec(v_unused_645_);
v___x_623_ = v_toApplicative_614_;
v_isShared_624_ = v_isSharedCheck_644_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_toSeqRight_621_);
lean_inc(v_toSeqLeft_620_);
lean_inc(v_toSeq_619_);
lean_inc(v_toFunctor_618_);
lean_dec(v_toApplicative_614_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_644_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___x_634_; 
v___f_625_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_626_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_618_);
v___f_627_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_627_, 0, v_toFunctor_618_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_628_, 0, v_toFunctor_618_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___f_627_);
lean_ctor_set(v___x_629_, 1, v___f_628_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeqRight_621_);
v___f_631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_631_, 0, v_toSeqLeft_620_);
v___f_632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_632_, 0, v_toSeq_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___f_630_);
lean_ctor_set(v___x_623_, 3, v___f_631_);
lean_ctor_set(v___x_623_, 2, v___f_632_);
lean_ctor_set(v___x_623_, 1, v___f_625_);
lean_ctor_set(v___x_623_, 0, v___x_629_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___f_625_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v___f_632_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v___f_631_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v___f_630_);
v___x_634_ = v_reuseFailAlloc_643_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___f_626_);
lean_ctor_set(v___x_616_, 0, v___x_634_);
v___x_636_ = v___x_616_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___f_626_);
v___x_636_ = v_reuseFailAlloc_642_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_14784__overap_640_; lean_object* v___x_641_; 
v___x_637_ = l_StateRefT_x27_instMonad___redArg(v___x_636_);
v___x_638_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_639_ = l_instInhabitedOfMonad___redArg(v___x_637_, v___x_638_);
v___x_14784__overap_640_ = lean_panic_fn_borrowed(v___x_639_, v_msg_607_);
lean_dec(v___x_639_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
v___x_641_ = lean_apply_4(v___x_14784__overap_640_, v___y_608_, v___y_609_, v___y_610_, lean_box(0));
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_654_, size_t v_i_655_, lean_object* v_bs_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_655_, v_sz_654_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_bs_656_);
return v___x_660_;
}
else
{
lean_object* v_v_661_; lean_object* v___x_662_; lean_object* v_bs_x27_663_; lean_object* v___x_664_; 
v_v_661_ = lean_array_uget(v_bs_656_, v_i_655_);
v___x_662_ = lean_unsigned_to_nat(0u);
v_bs_x27_663_ = lean_array_uset(v_bs_656_, v_i_655_, v___x_662_);
v___x_664_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_661_, v___y_657_);
lean_dec(v_v_661_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_655_, v___x_666_);
v___x_668_ = lean_array_uset(v_bs_x27_663_, v_i_655_, v_a_665_);
v_i_655_ = v___x_667_;
v_bs_656_ = v___x_668_;
goto _start;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_bs_x27_663_);
v_a_670_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_664_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_678_, lean_object* v_i_679_, lean_object* v_bs_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_684_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_683_, v_i_boxed_684_, v_bs_680_, v___y_681_);
lean_dec(v___y_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_686_, size_t v_i_687_, lean_object* v_bs_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_687_, v_sz_686_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_bs_688_);
return v___x_692_;
}
else
{
lean_object* v_v_693_; lean_object* v___x_694_; lean_object* v_bs_x27_695_; lean_object* v___x_696_; 
v_v_693_ = lean_array_uget(v_bs_688_, v_i_687_);
v___x_694_ = lean_unsigned_to_nat(0u);
v_bs_x27_695_ = lean_array_uset(v_bs_688_, v_i_687_, v___x_694_);
v___x_696_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_693_, v___y_689_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_687_, v___x_698_);
v___x_700_ = lean_array_uset(v_bs_x27_695_, v_i_687_, v_a_697_);
v_i_687_ = v___x_699_;
v_bs_688_ = v___x_700_;
goto _start;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_bs_x27_695_);
v_a_702_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_696_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_696_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_716_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_715_, v_i_boxed_716_, v_bs_712_, v___y_713_);
lean_dec(v___y_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_args_718_, lean_object* v_fvarId_719_, lean_object* v_k_720_, lean_object* v_id_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
size_t v_sz_726_; size_t v___x_727_; lean_object* v___x_728_; 
v_sz_726_ = lean_array_size(v_args_718_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_726_, v___x_727_, v_args_718_, v___y_722_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_719_, v___y_722_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_IR_ToIR_lowerCode(v_k_720_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v___x_737_, 0, v_a_731_);
lean_ctor_set(v___x_737_, 1, v_a_733_);
lean_ctor_set(v___x_737_, 2, v_id_721_);
lean_ctor_set(v___x_737_, 3, v_a_729_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
else
{
lean_dec(v_a_731_);
lean_dec(v_a_729_);
lean_dec(v_id_721_);
return v___x_732_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_729_);
lean_dec(v_id_721_);
lean_dec_ref(v_k_720_);
v_a_742_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_730_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_730_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_id_721_);
lean_dec_ref(v_k_720_);
lean_dec(v_fvarId_719_);
v_a_750_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_728_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_728_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_args_758_, lean_object* v_fvarId_759_, lean_object* v_k_760_, lean_object* v_id_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_args_758_, v_fvarId_759_, v_k_760_, v_id_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_767_, lean_object* v_k_768_, lean_object* v_fvarId_769_, lean_object* v_f_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_769_, v_a_771_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
if (lean_obj_tag(v_a_776_) == 0)
{
lean_object* v_id_777_; lean_object* v___x_778_; 
lean_dec_ref(v_k_768_);
lean_dec_ref(v_decl_767_);
v_id_777_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_id_777_);
lean_dec_ref_known(v_a_776_, 1);
lean_inc(v_a_773_);
lean_inc_ref(v_a_772_);
lean_inc(v_a_771_);
v___x_778_ = lean_apply_5(v_f_770_, v_id_777_, v_a_771_, v_a_772_, v_a_773_, lean_box(0));
return v___x_778_;
}
else
{
lean_object* v___x_779_; 
lean_dec_ref(v_f_770_);
v___x_779_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_767_, v_k_768_, v_a_771_, v_a_772_, v_a_773_);
return v___x_779_;
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_f_770_);
lean_dec_ref(v_k_768_);
lean_dec_ref(v_decl_767_);
v_a_780_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_775_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_775_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_fvarId_788_, lean_object* v_k_789_, lean_object* v_i_790_, lean_object* v_var_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_788_, v___y_792_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_Lean_IR_ToIR_lowerCode(v_k_789_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_807_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_803_, 0, v_a_797_);
lean_ctor_set(v___x_803_, 1, v_a_799_);
lean_ctor_set(v___x_803_, 2, v_i_790_);
lean_ctor_set(v___x_803_, 3, v_var_791_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_dec(v_a_797_);
lean_dec(v_var_791_);
lean_dec(v_i_790_);
return v___x_798_;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_var_791_);
lean_dec(v_i_790_);
lean_dec_ref(v_k_789_);
v_a_808_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_796_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_796_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
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
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_fvarId_816_, lean_object* v_k_817_, lean_object* v_i_818_, lean_object* v_var_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_fvarId_816_, v_k_817_, v_i_818_, v_var_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_fvarId_825_, lean_object* v_k_826_, lean_object* v_i_827_, lean_object* v_var_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_825_, v___y_829_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_IR_ToIR_lowerCode(v_k_826_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_844_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_844_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_840_, 0, v_a_834_);
lean_ctor_set(v___x_840_, 1, v_a_836_);
lean_ctor_set(v___x_840_, 2, v_i_827_);
lean_ctor_set(v___x_840_, 3, v_var_828_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_dec(v_a_834_);
lean_dec(v_var_828_);
lean_dec(v_i_827_);
return v___x_835_;
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_var_828_);
lean_dec(v_i_827_);
lean_dec_ref(v_k_826_);
v_a_845_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_833_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_833_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_fvarId_853_, lean_object* v_k_854_, lean_object* v_i_855_, lean_object* v_var_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_fvarId_853_, v_k_854_, v_i_855_, v_var_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_fvarId_862_, lean_object* v_k_863_, lean_object* v_type_864_, lean_object* v_n_865_, lean_object* v_offset_866_, lean_object* v_var_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_862_, v___y_868_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = l_Lean_IR_ToIR_lowerCode(v_k_863_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v___x_879_, 0, v_a_873_);
lean_ctor_set(v___x_879_, 1, v_a_875_);
lean_ctor_set(v___x_879_, 2, v_type_864_);
lean_ctor_set(v___x_879_, 3, v_n_865_);
lean_ctor_set(v___x_879_, 4, v_offset_866_);
lean_ctor_set(v___x_879_, 5, v_var_867_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_dec(v_a_873_);
lean_dec(v_var_867_);
lean_dec(v_offset_866_);
lean_dec(v_n_865_);
lean_dec(v_type_864_);
return v___x_874_;
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_var_867_);
lean_dec(v_offset_866_);
lean_dec(v_n_865_);
lean_dec(v_type_864_);
lean_dec_ref(v_k_863_);
v_a_884_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_872_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_872_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_fvarId_892_, lean_object* v_k_893_, lean_object* v_type_894_, lean_object* v_n_895_, lean_object* v_offset_896_, lean_object* v_var_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_fvarId_892_, v_k_893_, v_type_894_, v_n_895_, v_offset_896_, v_var_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_fvarId_903_, lean_object* v_k_904_, lean_object* v_n_905_, lean_object* v_var_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_903_, v___y_907_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_IR_ToIR_lowerCode(v_k_904_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_918_, 0, v_a_912_);
lean_ctor_set(v___x_918_, 1, v_a_914_);
lean_ctor_set(v___x_918_, 2, v_n_905_);
lean_ctor_set(v___x_918_, 3, v_var_906_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_dec(v_a_912_);
lean_dec(v_var_906_);
lean_dec(v_n_905_);
return v___x_913_;
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_var_906_);
lean_dec(v_n_905_);
lean_dec_ref(v_k_904_);
v_a_923_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_911_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_911_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_fvarId_931_, lean_object* v_k_932_, lean_object* v_n_933_, lean_object* v_var_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_fvarId_931_, v_k_932_, v_n_933_, v_var_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_args_940_, lean_object* v_fvarId_941_, lean_object* v_k_942_, lean_object* v_i_943_, uint8_t v_updateHeader_944_, lean_object* v_var_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_sz_950_ = lean_array_size(v_args_940_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_950_, v___x_951_, v_args_940_, v___y_946_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_941_, v___y_946_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = l_Lean_IR_ToIR_lowerCode(v_k_942_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_977_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_977_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_977_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_977_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_name_961_; lean_object* v_cidx_962_; lean_object* v_size_963_; lean_object* v_usize_964_; lean_object* v_ssize_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_976_; 
v_name_961_ = lean_ctor_get(v_i_943_, 0);
v_cidx_962_ = lean_ctor_get(v_i_943_, 1);
v_size_963_ = lean_ctor_get(v_i_943_, 2);
v_usize_964_ = lean_ctor_get(v_i_943_, 3);
v_ssize_965_ = lean_ctor_get(v_i_943_, 4);
v_isSharedCheck_976_ = !lean_is_exclusive(v_i_943_);
if (v_isSharedCheck_976_ == 0)
{
v___x_967_ = v_i_943_;
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_ssize_965_);
lean_inc(v_usize_964_);
lean_inc(v_size_963_);
lean_inc(v_cidx_962_);
lean_inc(v_name_961_);
lean_dec(v_i_943_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_name_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_cidx_962_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_size_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_usize_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_ssize_965_);
v___x_970_ = v_reuseFailAlloc_975_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v___x_971_, 0, v_a_955_);
lean_ctor_set(v___x_971_, 1, v_a_957_);
lean_ctor_set(v___x_971_, 2, v_var_945_);
lean_ctor_set(v___x_971_, 3, v___x_970_);
lean_ctor_set(v___x_971_, 4, v_a_953_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*5, v_updateHeader_944_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_971_);
v___x_973_ = v___x_959_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
else
{
lean_dec(v_a_955_);
lean_dec(v_a_953_);
lean_dec(v_var_945_);
lean_dec_ref(v_i_943_);
return v___x_956_;
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_a_953_);
lean_dec(v_var_945_);
lean_dec_ref(v_i_943_);
lean_dec_ref(v_k_942_);
v_a_978_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_954_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_954_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_var_945_);
lean_dec_ref(v_i_943_);
lean_dec_ref(v_k_942_);
lean_dec(v_fvarId_941_);
v_a_986_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_952_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_952_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_args_994_, lean_object* v_fvarId_995_, lean_object* v_k_996_, lean_object* v_i_997_, lean_object* v_updateHeader_998_, lean_object* v_var_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_updateHeader_16090__boxed_1004_; lean_object* v_res_1005_; 
v_updateHeader_16090__boxed_1004_ = lean_unbox(v_updateHeader_998_);
v_res_1005_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_args_994_, v_fvarId_995_, v_k_996_, v_i_997_, v_updateHeader_16090__boxed_1004_, v_var_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_fvarId_1006_, lean_object* v_k_1007_, lean_object* v_ty_1008_, lean_object* v_var_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1006_, v___y_1010_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = l_Lean_IR_ToIR_lowerCode(v_k_1007_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1026_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1021_ = l_Lean_IR_toIRType(v_ty_1008_);
v___x_1022_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v___x_1022_, 0, v_a_1015_);
lean_ctor_set(v___x_1022_, 1, v_a_1017_);
lean_ctor_set(v___x_1022_, 2, v___x_1021_);
lean_ctor_set(v___x_1022_, 3, v_var_1009_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1022_);
v___x_1024_ = v___x_1019_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_dec(v_a_1015_);
lean_dec(v_var_1009_);
return v___x_1016_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_var_1009_);
lean_dec_ref(v_k_1007_);
v_a_1027_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1014_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1014_);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_fvarId_1035_, lean_object* v_k_1036_, lean_object* v_ty_1037_, lean_object* v_var_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_fvarId_1035_, v_k_1036_, v_ty_1037_, v_var_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v_ty_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_fvarId_1044_, lean_object* v_k_1045_, lean_object* v_type_1046_, lean_object* v_var_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1044_, v___y_1048_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = l_Lean_IR_ToIR_lowerCode(v_k_1045_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1059_, 0, v_a_1053_);
lean_ctor_set(v___x_1059_, 1, v_a_1055_);
lean_ctor_set(v___x_1059_, 2, v_type_1046_);
lean_ctor_set(v___x_1059_, 3, v_var_1047_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_dec(v_a_1053_);
lean_dec(v_var_1047_);
lean_dec(v_type_1046_);
return v___x_1054_;
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_var_1047_);
lean_dec(v_type_1046_);
lean_dec_ref(v_k_1045_);
v_a_1064_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1052_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1052_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_fvarId_1072_, lean_object* v_k_1073_, lean_object* v_type_1074_, lean_object* v_var_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_fvarId_1072_, v_k_1073_, v_type_1074_, v_var_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_fvarId_1081_, lean_object* v_k_1082_, lean_object* v_var_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1081_, v___y_1084_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_IR_ToIR_lowerCode(v_k_1082_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1089_);
lean_ctor_set(v___x_1095_, 1, v_a_1091_);
lean_ctor_set(v___x_1095_, 2, v_var_1083_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_dec(v_a_1089_);
lean_dec(v_var_1083_);
return v___x_1090_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_var_1083_);
lean_dec_ref(v_k_1082_);
v_a_1100_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1088_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1088_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_fvarId_1108_, lean_object* v_k_1109_, lean_object* v_var_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_fvarId_1108_, v_k_1109_, v_var_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_1116_, lean_object* v_k_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_fvarId_1122_; lean_object* v_type_1123_; lean_object* v_value_1124_; lean_object* v_type_1125_; 
v_fvarId_1122_ = lean_ctor_get(v_decl_1116_, 0);
v_type_1123_ = lean_ctor_get(v_decl_1116_, 2);
v_value_1124_ = lean_ctor_get(v_decl_1116_, 3);
v_type_1125_ = l_Lean_IR_toIRType(v_type_1123_);
switch(lean_obj_tag(v_value_1124_))
{
case 0:
{
lean_object* v_value_1126_; 
lean_inc_ref(v_value_1124_);
lean_inc(v_fvarId_1122_);
lean_dec(v_type_1125_);
lean_dec_ref(v_decl_1116_);
v_value_1126_ = lean_ctor_get(v_value_1124_, 0);
lean_inc_ref(v_value_1126_);
lean_dec_ref_known(v_value_1124_, 1);
switch(lean_obj_tag(v_value_1126_))
{
case 0:
{
lean_object* v_val_1127_; lean_object* v___x_1128_; 
v_val_1127_ = lean_ctor_get(v_value_1126_, 0);
lean_inc(v_val_1127_);
lean_dec_ref_known(v_value_1126_, 1);
v___x_1128_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v___x_1135_, 0, v_a_1129_);
lean_ctor_set(v___x_1135_, 1, v_a_1131_);
lean_ctor_set(v___x_1135_, 2, v_val_1127_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_dec(v_a_1129_);
lean_dec(v_val_1127_);
return v___x_1130_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_val_1127_);
lean_dec_ref(v_k_1117_);
v_a_1140_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1128_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1128_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
case 1:
{
lean_object* v_val_1148_; lean_object* v___x_1149_; 
v_val_1148_ = lean_ctor_get(v_value_1126_, 0);
lean_inc_ref(v_val_1148_);
lean_dec_ref_known(v_value_1126_, 1);
v___x_1149_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1150_);
lean_ctor_set(v___x_1156_, 1, v_a_1152_);
lean_ctor_set(v___x_1156_, 2, v_val_1148_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
lean_dec(v_a_1150_);
lean_dec_ref(v_val_1148_);
return v___x_1151_;
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_val_1148_);
lean_dec_ref(v_k_1117_);
v_a_1161_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1149_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1149_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
case 2:
{
uint8_t v_val_1169_; lean_object* v___x_1170_; 
v_val_1169_ = lean_ctor_get_uint8(v_value_1126_, 0);
lean_dec_ref_known(v_value_1126_, 0);
v___x_1170_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v___x_1177_, 0, v_a_1171_);
lean_ctor_set(v___x_1177_, 1, v_a_1173_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*2, v_val_1169_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_dec(v_a_1171_);
return v___x_1172_;
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_k_1117_);
v_a_1182_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1170_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1170_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
case 3:
{
uint16_t v_val_1190_; lean_object* v___x_1191_; 
v_val_1190_ = lean_ctor_get_uint16(v_value_1126_, 0);
lean_dec_ref_known(v_value_1126_, 0);
v___x_1191_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1202_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v___x_1198_, 0, v_a_1192_);
lean_ctor_set(v___x_1198_, 1, v_a_1194_);
lean_ctor_set_uint16(v___x_1198_, sizeof(void*)*2, v_val_1190_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
lean_dec(v_a_1192_);
return v___x_1193_;
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_k_1117_);
v_a_1203_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1191_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1191_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
case 4:
{
uint32_t v_val_1211_; lean_object* v___x_1212_; 
v_val_1211_ = lean_ctor_get_uint32(v_value_1126_, 0);
lean_dec_ref_known(v_value_1126_, 0);
v___x_1212_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v___x_1219_, 0, v_a_1213_);
lean_ctor_set(v___x_1219_, 1, v_a_1215_);
lean_ctor_set_uint32(v___x_1219_, sizeof(void*)*2, v_val_1211_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_dec(v_a_1213_);
return v___x_1214_;
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v_k_1117_);
v_a_1224_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1212_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1212_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
case 5:
{
uint64_t v_val_1232_; lean_object* v___x_1233_; 
v_val_1232_ = lean_ctor_get_uint64(v_value_1126_, 0);
lean_dec_ref_known(v_value_1126_, 0);
v___x_1233_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v___x_1240_, 0, v_a_1234_);
lean_ctor_set(v___x_1240_, 1, v_a_1236_);
lean_ctor_set_uint64(v___x_1240_, sizeof(void*)*2, v_val_1232_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_dec(v_a_1234_);
return v___x_1235_;
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_k_1117_);
v_a_1245_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1233_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1233_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
default: 
{
uint64_t v_val_1253_; lean_object* v___x_1254_; 
v_val_1253_ = lean_ctor_get_uint64(v_value_1126_, 0);
lean_dec_ref_known(v_value_1126_, 0);
v___x_1254_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v___x_1261_, 0, v_a_1255_);
lean_ctor_set(v___x_1261_, 1, v_a_1257_);
lean_ctor_set_uint64(v___x_1261_, sizeof(void*)*2, v_val_1253_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_dec(v_a_1255_);
return v___x_1256_;
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_k_1117_);
v_a_1266_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1254_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1254_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_1274_; 
lean_dec(v_type_1125_);
v___x_1274_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1116_, v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
return v___x_1274_;
}
case 4:
{
lean_object* v_fvarId_1275_; lean_object* v_args_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; 
lean_dec(v_type_1125_);
v_fvarId_1275_ = lean_ctor_get(v_value_1124_, 0);
lean_inc(v_fvarId_1275_);
v_args_1276_ = lean_ctor_get(v_value_1124_, 1);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
lean_inc_ref(v_args_1276_);
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1277_, 0, v_args_1276_);
lean_closure_set(v___f_1277_, 1, v_fvarId_1122_);
lean_closure_set(v___f_1277_, 2, v_k_1117_);
v___x_1278_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_fvarId_1275_, v___f_1277_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_fvarId_1275_);
return v___x_1278_;
}
case 5:
{
lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1330_; 
lean_inc_ref(v_value_1124_);
lean_inc(v_fvarId_1122_);
lean_dec(v_type_1125_);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_decl_1116_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; lean_object* v_unused_1332_; lean_object* v_unused_1333_; lean_object* v_unused_1334_; 
v_unused_1331_ = lean_ctor_get(v_decl_1116_, 3);
lean_dec(v_unused_1331_);
v_unused_1332_ = lean_ctor_get(v_decl_1116_, 2);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_decl_1116_, 1);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v_decl_1116_, 0);
lean_dec(v_unused_1334_);
v___x_1280_ = v_decl_1116_;
v_isShared_1281_ = v_isSharedCheck_1330_;
goto v_resetjp_1279_;
}
else
{
lean_dec(v_decl_1116_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1330_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_i_1282_; lean_object* v_args_1283_; size_t v_sz_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v_i_1282_ = lean_ctor_get(v_value_1124_, 0);
lean_inc_ref(v_i_1282_);
v_args_1283_ = lean_ctor_get(v_value_1124_, 1);
lean_inc_ref(v_args_1283_);
lean_dec_ref_known(v_value_1124_, 2);
v_sz_1284_ = lean_array_size(v_args_1283_);
v___x_1285_ = ((size_t)0ULL);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1284_, v___x_1285_, v_args_1283_, v_a_1118_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1290_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1313_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1313_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1313_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_name_1295_; lean_object* v_cidx_1296_; lean_object* v_size_1297_; lean_object* v_usize_1298_; lean_object* v_ssize_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1312_; 
v_name_1295_ = lean_ctor_get(v_i_1282_, 0);
v_cidx_1296_ = lean_ctor_get(v_i_1282_, 1);
v_size_1297_ = lean_ctor_get(v_i_1282_, 2);
v_usize_1298_ = lean_ctor_get(v_i_1282_, 3);
v_ssize_1299_ = lean_ctor_get(v_i_1282_, 4);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_i_1282_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1301_ = v_i_1282_;
v_isShared_1302_ = v_isSharedCheck_1312_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_ssize_1299_);
lean_inc(v_usize_1298_);
lean_inc(v_size_1297_);
lean_inc(v_cidx_1296_);
lean_inc(v_name_1295_);
lean_dec(v_i_1282_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1312_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_name_1295_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_cidx_1296_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_size_1297_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_usize_1298_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_ssize_1299_);
v___x_1304_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 3, v_a_1287_);
lean_ctor_set(v___x_1280_, 2, v___x_1304_);
lean_ctor_set(v___x_1280_, 1, v_a_1291_);
lean_ctor_set(v___x_1280_, 0, v_a_1289_);
v___x_1306_ = v___x_1280_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1289_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_a_1291_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_a_1287_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1306_);
v___x_1308_ = v___x_1293_;
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
}
}
else
{
lean_dec(v_a_1289_);
lean_dec(v_a_1287_);
lean_dec_ref(v_i_1282_);
lean_del_object(v___x_1280_);
return v___x_1290_;
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_a_1287_);
lean_dec_ref(v_i_1282_);
lean_del_object(v___x_1280_);
lean_dec_ref(v_k_1117_);
v_a_1314_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1288_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1288_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_i_1282_);
lean_del_object(v___x_1280_);
lean_dec(v_fvarId_1122_);
lean_dec_ref(v_k_1117_);
v_a_1322_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1286_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1286_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1335_; lean_object* v_var_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; 
lean_dec(v_type_1125_);
v_i_1335_ = lean_ctor_get(v_value_1124_, 0);
v_var_1336_ = lean_ctor_get(v_value_1124_, 1);
lean_inc(v_var_1336_);
lean_inc(v_i_1335_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1337_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1337_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1337_, 1, v_k_1117_);
lean_closure_set(v___f_1337_, 2, v_i_1335_);
v___x_1338_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_var_1336_, v___f_1337_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_var_1336_);
return v___x_1338_;
}
case 7:
{
lean_object* v_i_1339_; lean_object* v_var_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; 
lean_dec(v_type_1125_);
v_i_1339_ = lean_ctor_get(v_value_1124_, 0);
v_var_1340_ = lean_ctor_get(v_value_1124_, 1);
lean_inc(v_var_1340_);
lean_inc(v_i_1339_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 8, 3);
lean_closure_set(v___f_1341_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1341_, 1, v_k_1117_);
lean_closure_set(v___f_1341_, 2, v_i_1339_);
v___x_1342_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_var_1340_, v___f_1341_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_var_1340_);
return v___x_1342_;
}
case 8:
{
lean_object* v_n_1343_; lean_object* v_offset_1344_; lean_object* v_var_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; 
v_n_1343_ = lean_ctor_get(v_value_1124_, 0);
v_offset_1344_ = lean_ctor_get(v_value_1124_, 1);
v_var_1345_ = lean_ctor_get(v_value_1124_, 2);
lean_inc(v_var_1345_);
lean_inc(v_offset_1344_);
lean_inc(v_n_1343_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 10, 5);
lean_closure_set(v___f_1346_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1346_, 1, v_k_1117_);
lean_closure_set(v___f_1346_, 2, v_type_1125_);
lean_closure_set(v___f_1346_, 3, v_n_1343_);
lean_closure_set(v___f_1346_, 4, v_offset_1344_);
v___x_1347_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_var_1345_, v___f_1346_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_var_1345_);
return v___x_1347_;
}
case 9:
{
lean_object* v_fn_1348_; lean_object* v_args_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
lean_inc_ref(v_value_1124_);
lean_inc(v_fvarId_1122_);
lean_dec_ref(v_decl_1116_);
v_fn_1348_ = lean_ctor_get(v_value_1124_, 0);
lean_inc(v_fn_1348_);
v_args_1349_ = lean_ctor_get(v_value_1124_, 1);
lean_inc_ref(v_args_1349_);
lean_dec_ref_known(v_value_1124_, 2);
v_sz_1350_ = lean_array_size(v_args_1349_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1350_, v___x_1351_, v_args_1349_, v_a_1118_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v___x_1361_, 0, v_a_1355_);
lean_ctor_set(v___x_1361_, 1, v_a_1357_);
lean_ctor_set(v___x_1361_, 2, v_type_1125_);
lean_ctor_set(v___x_1361_, 3, v_fn_1348_);
lean_ctor_set(v___x_1361_, 4, v_a_1353_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
lean_dec(v_a_1355_);
lean_dec(v_a_1353_);
lean_dec(v_fn_1348_);
lean_dec(v_type_1125_);
return v___x_1356_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1353_);
lean_dec(v_fn_1348_);
lean_dec(v_type_1125_);
lean_dec_ref(v_k_1117_);
v_a_1366_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1354_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1354_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_fn_1348_);
lean_dec(v_type_1125_);
lean_dec(v_fvarId_1122_);
lean_dec_ref(v_k_1117_);
v_a_1374_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1352_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1352_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
case 10:
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1421_; 
lean_inc_ref(v_value_1124_);
lean_inc(v_fvarId_1122_);
lean_dec(v_type_1125_);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_decl_1116_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; 
v_unused_1422_ = lean_ctor_get(v_decl_1116_, 3);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_decl_1116_, 2);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_decl_1116_, 1);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_decl_1116_, 0);
lean_dec(v_unused_1425_);
v___x_1383_ = v_decl_1116_;
v_isShared_1384_ = v_isSharedCheck_1421_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_decl_1116_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1421_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_fn_1385_; lean_object* v_args_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_fn_1385_ = lean_ctor_get(v_value_1124_, 0);
lean_inc(v_fn_1385_);
v_args_1386_ = lean_ctor_get(v_value_1124_, 1);
lean_inc_ref(v_args_1386_);
lean_dec_ref_known(v_value_1124_, 2);
v_sz_1387_ = lean_array_size(v_args_1386_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1387_, v___x_1388_, v_args_1386_, v_a_1118_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1122_, v_a_1118_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Lean_IR_ToIR_lowerCode(v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1404_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1404_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1404_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 7);
lean_ctor_set(v___x_1383_, 3, v_a_1390_);
lean_ctor_set(v___x_1383_, 2, v_fn_1385_);
lean_ctor_set(v___x_1383_, 1, v_a_1394_);
lean_ctor_set(v___x_1383_, 0, v_a_1392_);
v___x_1399_ = v___x_1383_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1392_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_a_1394_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_fn_1385_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_a_1390_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_dec(v_fn_1385_);
lean_del_object(v___x_1383_);
return v___x_1393_;
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_a_1390_);
lean_dec(v_fn_1385_);
lean_del_object(v___x_1383_);
lean_dec_ref(v_k_1117_);
v_a_1405_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1391_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1391_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_fn_1385_);
lean_del_object(v___x_1383_);
lean_dec(v_fvarId_1122_);
lean_dec_ref(v_k_1117_);
v_a_1413_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1389_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1389_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1426_; lean_object* v_var_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
lean_dec(v_type_1125_);
v_n_1426_ = lean_ctor_get(v_value_1124_, 0);
v_var_1427_ = lean_ctor_get(v_value_1124_, 1);
lean_inc(v_var_1427_);
lean_inc(v_n_1426_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1428_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1428_, 1, v_k_1117_);
lean_closure_set(v___f_1428_, 2, v_n_1426_);
v___x_1429_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_var_1427_, v___f_1428_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_var_1427_);
return v___x_1429_;
}
case 12:
{
lean_object* v_var_1430_; lean_object* v_i_1431_; uint8_t v_updateHeader_1432_; lean_object* v_args_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; 
lean_dec(v_type_1125_);
v_var_1430_ = lean_ctor_get(v_value_1124_, 0);
lean_inc(v_var_1430_);
v_i_1431_ = lean_ctor_get(v_value_1124_, 1);
v_updateHeader_1432_ = lean_ctor_get_uint8(v_value_1124_, sizeof(void*)*3);
v_args_1433_ = lean_ctor_get(v_value_1124_, 2);
v___x_1434_ = lean_box(v_updateHeader_1432_);
lean_inc_ref(v_i_1431_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
lean_inc_ref(v_args_1433_);
v___f_1435_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 10, 5);
lean_closure_set(v___f_1435_, 0, v_args_1433_);
lean_closure_set(v___f_1435_, 1, v_fvarId_1122_);
lean_closure_set(v___f_1435_, 2, v_k_1117_);
lean_closure_set(v___f_1435_, 3, v_i_1431_);
lean_closure_set(v___f_1435_, 4, v___x_1434_);
v___x_1436_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_var_1430_, v___f_1435_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_var_1430_);
return v___x_1436_;
}
case 13:
{
lean_object* v_ty_1437_; lean_object* v_fvarId_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; 
lean_dec(v_type_1125_);
v_ty_1437_ = lean_ctor_get(v_value_1124_, 0);
v_fvarId_1438_ = lean_ctor_get(v_value_1124_, 1);
lean_inc(v_fvarId_1438_);
lean_inc_ref(v_ty_1437_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 8, 3);
lean_closure_set(v___f_1439_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1439_, 1, v_k_1117_);
lean_closure_set(v___f_1439_, 2, v_ty_1437_);
v___x_1440_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_fvarId_1438_, v___f_1439_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_fvarId_1438_);
return v___x_1440_;
}
case 14:
{
lean_object* v_fvarId_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; 
v_fvarId_1441_ = lean_ctor_get(v_value_1124_, 0);
lean_inc(v_fvarId_1441_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 8, 3);
lean_closure_set(v___f_1442_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1442_, 1, v_k_1117_);
lean_closure_set(v___f_1442_, 2, v_type_1125_);
v___x_1443_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_fvarId_1441_, v___f_1442_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_fvarId_1441_);
return v___x_1443_;
}
default: 
{
lean_object* v_fvarId_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; 
lean_dec(v_type_1125_);
v_fvarId_1444_ = lean_ctor_get(v_value_1124_, 0);
lean_inc(v_fvarId_1444_);
lean_inc_ref(v_k_1117_);
lean_inc(v_fvarId_1122_);
v___f_1445_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 7, 2);
lean_closure_set(v___f_1445_, 0, v_fvarId_1122_);
lean_closure_set(v___f_1445_, 1, v_k_1117_);
v___x_1446_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1116_, v_k_1117_, v_fvarId_1444_, v___f_1445_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_fvarId_1444_);
return v___x_1446_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1450_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1451_ = lean_unsigned_to_nat(15u);
v___x_1452_ = lean_unsigned_to_nat(129u);
v___x_1453_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1454_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1455_ = l_mkPanicMessageWithDecl(v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
if (lean_obj_tag(v_a_1456_) == 1)
{
lean_object* v_info_1461_; lean_object* v_code_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1498_; 
v_info_1461_ = lean_ctor_get(v_a_1456_, 0);
v_code_1462_ = lean_ctor_get(v_a_1456_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_a_1456_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1464_ = v_a_1456_;
v_isShared_1465_ = v_isSharedCheck_1498_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_code_1462_);
lean_inc(v_info_1461_);
lean_dec(v_a_1456_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1498_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_IR_ToIR_lowerCode(v_code_1462_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1489_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1489_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1489_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_name_1471_; lean_object* v_cidx_1472_; lean_object* v_size_1473_; lean_object* v_usize_1474_; lean_object* v_ssize_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1488_; 
v_name_1471_ = lean_ctor_get(v_info_1461_, 0);
v_cidx_1472_ = lean_ctor_get(v_info_1461_, 1);
v_size_1473_ = lean_ctor_get(v_info_1461_, 2);
v_usize_1474_ = lean_ctor_get(v_info_1461_, 3);
v_ssize_1475_ = lean_ctor_get(v_info_1461_, 4);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_info_1461_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1477_ = v_info_1461_;
v_isShared_1478_ = v_isSharedCheck_1488_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_ssize_1475_);
lean_inc(v_usize_1474_);
lean_inc(v_size_1473_);
lean_inc(v_cidx_1472_);
lean_inc(v_name_1471_);
lean_dec(v_info_1461_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1488_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_name_1471_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_cidx_1472_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_size_1473_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v_usize_1474_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v_ssize_1475_);
v___x_1480_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 0);
lean_ctor_set(v___x_1464_, 1, v_a_1467_);
lean_ctor_set(v___x_1464_, 0, v___x_1480_);
v___x_1482_ = v___x_1464_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_a_1467_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1482_);
v___x_1484_ = v___x_1469_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
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
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_del_object(v___x_1464_);
lean_dec_ref(v_info_1461_);
v_a_1490_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1466_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1466_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_code_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1523_; 
v_code_1499_ = lean_ctor_get(v_a_1456_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_a_1456_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1501_ = v_a_1456_;
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_code_1499_);
lean_dec(v_a_1456_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_IR_ToIR_lowerCode(v_code_1499_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set_tag(v___x_1501_, 1);
lean_ctor_set(v___x_1501_, 0, v_a_1504_);
v___x_1509_ = v___x_1501_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_del_object(v___x_1501_);
v_a_1515_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1503_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1503_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1524_, size_t v_i_1525_, lean_object* v_bs_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_lt(v_i_1525_, v_sz_1524_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_bs_1526_);
return v___x_1532_;
}
else
{
lean_object* v_v_1533_; lean_object* v___x_1534_; lean_object* v_bs_x27_1535_; lean_object* v___x_1536_; 
v_v_1533_ = lean_array_uget(v_bs_1526_, v_i_1525_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v_bs_x27_1535_ = lean_array_uset(v_bs_1526_, v_i_1525_, v___x_1534_);
v___x_1536_ = l_Lean_IR_ToIR_lowerAlt(v_v_1533_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1525_, v___x_1538_);
v___x_1540_ = lean_array_uset(v_bs_x27_1535_, v_i_1525_, v_a_1537_);
v_i_1525_ = v___x_1539_;
v_bs_1526_ = v___x_1540_;
goto _start;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_bs_x27_1535_);
v_a_1542_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1536_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1536_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1551_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1552_ = lean_unsigned_to_nat(53u);
v___x_1553_ = lean_unsigned_to_nat(96u);
v___x_1554_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1555_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1556_ = l_mkPanicMessageWithDecl(v___x_1555_, v___x_1554_, v___x_1553_, v___x_1552_, v___x_1551_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1557_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1558_ = lean_unsigned_to_nat(44u);
v___x_1559_ = lean_unsigned_to_nat(107u);
v___x_1560_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1561_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1562_ = l_mkPanicMessageWithDecl(v___x_1561_, v___x_1560_, v___x_1559_, v___x_1558_, v___x_1557_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1563_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1564_ = lean_unsigned_to_nat(44u);
v___x_1565_ = lean_unsigned_to_nat(115u);
v___x_1566_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1567_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1568_ = l_mkPanicMessageWithDecl(v___x_1567_, v___x_1566_, v___x_1565_, v___x_1564_, v___x_1563_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1569_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1570_ = lean_unsigned_to_nat(34u);
v___x_1571_ = lean_unsigned_to_nat(114u);
v___x_1572_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1573_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1574_ = l_mkPanicMessageWithDecl(v___x_1573_, v___x_1572_, v___x_1571_, v___x_1570_, v___x_1569_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1575_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1576_ = lean_unsigned_to_nat(44u);
v___x_1577_ = lean_unsigned_to_nat(111u);
v___x_1578_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1579_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1580_ = l_mkPanicMessageWithDecl(v___x_1579_, v___x_1578_, v___x_1577_, v___x_1576_, v___x_1575_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1581_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1582_ = lean_unsigned_to_nat(34u);
v___x_1583_ = lean_unsigned_to_nat(110u);
v___x_1584_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1585_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1586_ = l_mkPanicMessageWithDecl(v___x_1585_, v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1588_ = lean_unsigned_to_nat(41u);
v___x_1589_ = lean_unsigned_to_nat(118u);
v___x_1590_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1591_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1592_ = l_mkPanicMessageWithDecl(v___x_1591_, v___x_1590_, v___x_1589_, v___x_1588_, v___x_1587_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1593_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1594_ = lean_unsigned_to_nat(41u);
v___x_1595_ = lean_unsigned_to_nat(121u);
v___x_1596_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1597_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1598_ = l_mkPanicMessageWithDecl(v___x_1597_, v___x_1596_, v___x_1595_, v___x_1594_, v___x_1593_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1600_ = lean_unsigned_to_nat(41u);
v___x_1601_ = lean_unsigned_to_nat(124u);
v___x_1602_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1603_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1604_ = l_mkPanicMessageWithDecl(v___x_1603_, v___x_1602_, v___x_1601_, v___x_1600_, v___x_1599_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1606_ = lean_unsigned_to_nat(41u);
v___x_1607_ = lean_unsigned_to_nat(127u);
v___x_1608_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1609_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1610_ = l_mkPanicMessageWithDecl(v___x_1609_, v___x_1608_, v___x_1607_, v___x_1606_, v___x_1605_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
switch(lean_obj_tag(v_c_1611_))
{
case 0:
{
lean_object* v_decl_1616_; lean_object* v_k_1617_; lean_object* v___x_1618_; 
v_decl_1616_ = lean_ctor_get(v_c_1611_, 0);
lean_inc_ref(v_decl_1616_);
v_k_1617_ = lean_ctor_get(v_c_1611_, 1);
lean_inc_ref(v_k_1617_);
lean_dec_ref_known(v_c_1611_, 2);
v___x_1618_ = l_Lean_IR_ToIR_lowerLet(v_decl_1616_, v_k_1617_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1618_;
}
case 1:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec_ref_known(v_c_1611_, 2);
v___x_1619_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1620_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1619_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1620_;
}
case 2:
{
lean_object* v_decl_1621_; lean_object* v_k_1622_; lean_object* v_fvarId_1623_; lean_object* v_params_1624_; lean_object* v_value_1625_; lean_object* v___x_1626_; 
v_decl_1621_ = lean_ctor_get(v_c_1611_, 0);
lean_inc_ref(v_decl_1621_);
v_k_1622_ = lean_ctor_get(v_c_1611_, 1);
lean_inc_ref(v_k_1622_);
lean_dec_ref_known(v_c_1611_, 2);
v_fvarId_1623_ = lean_ctor_get(v_decl_1621_, 0);
lean_inc(v_fvarId_1623_);
v_params_1624_ = lean_ctor_get(v_decl_1621_, 2);
lean_inc_ref(v_params_1624_);
v_value_1625_ = lean_ctor_get(v_decl_1621_, 4);
lean_inc_ref(v_value_1625_);
lean_dec_ref(v_decl_1621_);
v___x_1626_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1623_, v_a_1612_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; size_t v_sz_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v_sz_1628_ = lean_array_size(v_params_1624_);
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1628_, v___x_1629_, v_params_1624_, v_a_1612_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = l_Lean_IR_ToIR_lowerCode(v_value_1625_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = l_Lean_IR_ToIR_lowerCode(v_k_1622_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1627_);
lean_ctor_set(v___x_1639_, 1, v_a_1631_);
lean_ctor_set(v___x_1639_, 2, v_a_1633_);
lean_ctor_set(v___x_1639_, 3, v_a_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_dec(v_a_1633_);
lean_dec(v_a_1631_);
lean_dec(v_a_1627_);
return v___x_1634_;
}
}
else
{
lean_dec(v_a_1631_);
lean_dec(v_a_1627_);
lean_dec_ref(v_k_1622_);
return v___x_1632_;
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_a_1627_);
lean_dec_ref(v_value_1625_);
lean_dec_ref(v_k_1622_);
v_a_1644_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1630_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1630_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_value_1625_);
lean_dec_ref(v_params_1624_);
lean_dec_ref(v_k_1622_);
v_a_1652_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1626_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1626_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1660_; lean_object* v_args_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1697_; 
v_fvarId_1660_ = lean_ctor_get(v_c_1611_, 0);
v_args_1661_ = lean_ctor_get(v_c_1611_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1663_ = v_c_1611_;
v_isShared_1664_ = v_isSharedCheck_1697_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_args_1661_);
lean_inc(v_fvarId_1660_);
lean_dec(v_c_1611_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1697_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1660_, v_a_1612_);
lean_dec(v_fvarId_1660_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; size_t v_sz_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v_sz_1667_ = lean_array_size(v_args_1661_);
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1667_, v___x_1668_, v_args_1661_, v_a_1612_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1680_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1680_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1680_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 29);
lean_ctor_set(v___x_1663_, 1, v_a_1670_);
lean_ctor_set(v___x_1663_, 0, v_a_1666_);
v___x_1675_ = v___x_1663_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(29, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1666_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1666_);
lean_del_object(v___x_1663_);
v_a_1681_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1669_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1669_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1663_);
lean_dec_ref(v_args_1661_);
v_a_1689_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1665_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1665_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1698_; lean_object* v_typeName_1699_; lean_object* v_discr_1700_; lean_object* v_alts_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1741_; 
v_cases_1698_ = lean_ctor_get(v_c_1611_, 0);
lean_inc_ref(v_cases_1698_);
lean_dec_ref_known(v_c_1611_, 1);
v_typeName_1699_ = lean_ctor_get(v_cases_1698_, 0);
v_discr_1700_ = lean_ctor_get(v_cases_1698_, 2);
v_alts_1701_ = lean_ctor_get(v_cases_1698_, 3);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_cases_1698_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_cases_1698_, 1);
lean_dec(v_unused_1742_);
v___x_1703_ = v_cases_1698_;
v_isShared_1704_ = v_isSharedCheck_1741_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_alts_1701_);
lean_inc(v_discr_1700_);
lean_inc(v_typeName_1699_);
lean_dec(v_cases_1698_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1741_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1700_, v_a_1612_);
lean_dec(v_discr_1700_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
if (lean_obj_tag(v_a_1706_) == 0)
{
lean_object* v_id_1707_; size_t v_sz_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_id_1707_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_id_1707_);
lean_dec_ref_known(v_a_1706_, 1);
v_sz_1708_ = lean_array_size(v_alts_1701_);
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1708_, v___x_1709_, v_alts_1701_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1722_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1722_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1722_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = l_Lean_IR_nameToIRType(v_typeName_1699_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 27);
lean_ctor_set(v___x_1703_, 3, v_a_1711_);
lean_ctor_set(v___x_1703_, 2, v___x_1715_);
lean_ctor_set(v___x_1703_, 1, v_id_1707_);
v___x_1717_ = v___x_1703_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(27, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_typeName_1699_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_id_1707_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_a_1711_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1717_);
v___x_1719_ = v___x_1713_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_id_1707_);
lean_del_object(v___x_1703_);
lean_dec(v_typeName_1699_);
v_a_1723_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1710_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1710_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_a_1706_);
lean_del_object(v___x_1703_);
lean_dec_ref(v_alts_1701_);
lean_dec(v_typeName_1699_);
v___x_1731_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1732_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1731_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1732_;
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_del_object(v___x_1703_);
lean_dec_ref(v_alts_1701_);
lean_dec(v_typeName_1699_);
v_a_1733_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1705_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1705_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1767_; 
v_fvarId_1743_ = lean_ctor_get(v_c_1611_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1745_ = v_c_1611_;
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_fvarId_1743_);
lean_dec(v_c_1611_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1743_, v_a_1612_);
lean_dec(v_fvarId_1743_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1758_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 28);
lean_ctor_set(v___x_1745_, 0, v_a_1748_);
v___x_1753_ = v___x_1745_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1753_);
v___x_1755_ = v___x_1750_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_del_object(v___x_1745_);
v_a_1759_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1747_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1747_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1775_; 
v_isSharedCheck_1775_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v_c_1611_, 0);
lean_dec(v_unused_1776_);
v___x_1769_ = v_c_1611_;
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v_c_1611_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = lean_box(30);
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1771_);
v___x_1773_ = v___x_1769_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
case 7:
{
lean_object* v_fvarId_1777_; lean_object* v_i_1778_; lean_object* v_y_1779_; lean_object* v_k_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1819_; 
v_fvarId_1777_ = lean_ctor_get(v_c_1611_, 0);
v_i_1778_ = lean_ctor_get(v_c_1611_, 1);
v_y_1779_ = lean_ctor_get(v_c_1611_, 2);
v_k_1780_ = lean_ctor_get(v_c_1611_, 3);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1782_ = v_c_1611_;
v_isShared_1783_ = v_isSharedCheck_1819_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_k_1780_);
lean_inc(v_y_1779_);
lean_inc(v_i_1778_);
lean_inc(v_fvarId_1777_);
lean_dec(v_c_1611_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1819_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1779_, v_a_1612_);
lean_dec(v_y_1779_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1777_, v_a_1612_);
lean_dec(v_fvarId_1777_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
if (lean_obj_tag(v_a_1787_) == 0)
{
lean_object* v_id_1788_; lean_object* v___x_1789_; 
v_id_1788_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_id_1788_);
lean_dec_ref_known(v_a_1787_, 1);
v___x_1789_ = l_Lean_IR_ToIR_lowerCode(v_k_1780_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 20);
lean_ctor_set(v___x_1782_, 3, v_a_1790_);
lean_ctor_set(v___x_1782_, 2, v_a_1785_);
lean_ctor_set(v___x_1782_, 0, v_id_1788_);
v___x_1795_ = v___x_1782_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(20, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_id_1788_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_i_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_a_1785_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1795_);
v___x_1797_ = v___x_1792_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_dec(v_id_1788_);
lean_dec(v_a_1785_);
lean_del_object(v___x_1782_);
lean_dec(v_i_1778_);
return v___x_1789_;
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v_a_1787_);
lean_dec(v_a_1785_);
lean_del_object(v___x_1782_);
lean_dec_ref(v_k_1780_);
lean_dec(v_i_1778_);
v___x_1801_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1802_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1801_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1802_;
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_a_1785_);
lean_del_object(v___x_1782_);
lean_dec_ref(v_k_1780_);
lean_dec(v_i_1778_);
v_a_1803_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1786_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1786_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_del_object(v___x_1782_);
lean_dec_ref(v_k_1780_);
lean_dec(v_i_1778_);
lean_dec(v_fvarId_1777_);
v_a_1811_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1784_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1784_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1820_; lean_object* v_i_1821_; lean_object* v_y_1822_; lean_object* v_k_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1865_; 
v_fvarId_1820_ = lean_ctor_get(v_c_1611_, 0);
v_i_1821_ = lean_ctor_get(v_c_1611_, 1);
v_y_1822_ = lean_ctor_get(v_c_1611_, 2);
v_k_1823_ = lean_ctor_get(v_c_1611_, 3);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1825_ = v_c_1611_;
v_isShared_1826_ = v_isSharedCheck_1865_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_k_1823_);
lean_inc(v_y_1822_);
lean_inc(v_i_1821_);
lean_inc(v_fvarId_1820_);
lean_dec(v_c_1611_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1865_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1822_, v_a_1612_);
lean_dec(v_y_1822_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
if (lean_obj_tag(v_a_1828_) == 0)
{
lean_object* v_id_1829_; lean_object* v___x_1830_; 
v_id_1829_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_id_1829_);
lean_dec_ref_known(v_a_1828_, 1);
v___x_1830_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1820_, v_a_1612_);
lean_dec(v_fvarId_1820_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
if (lean_obj_tag(v_a_1831_) == 0)
{
lean_object* v_id_1832_; lean_object* v___x_1833_; 
v_id_1832_ = lean_ctor_get(v_a_1831_, 0);
lean_inc(v_id_1832_);
lean_dec_ref_known(v_a_1831_, 1);
v___x_1833_ = l_Lean_IR_ToIR_lowerCode(v_k_1823_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1844_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 22);
lean_ctor_set(v___x_1825_, 3, v_a_1834_);
lean_ctor_set(v___x_1825_, 2, v_id_1829_);
lean_ctor_set(v___x_1825_, 0, v_id_1832_);
v___x_1839_ = v___x_1825_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_id_1832_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_i_1821_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_id_1829_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_dec(v_id_1832_);
lean_dec(v_id_1829_);
lean_del_object(v___x_1825_);
lean_dec(v_i_1821_);
return v___x_1833_;
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_a_1831_);
lean_dec(v_id_1829_);
lean_del_object(v___x_1825_);
lean_dec_ref(v_k_1823_);
lean_dec(v_i_1821_);
v___x_1845_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1846_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1845_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1846_;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_id_1829_);
lean_del_object(v___x_1825_);
lean_dec_ref(v_k_1823_);
lean_dec(v_i_1821_);
v_a_1847_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1830_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1830_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_a_1828_);
lean_del_object(v___x_1825_);
lean_dec_ref(v_k_1823_);
lean_dec(v_i_1821_);
lean_dec(v_fvarId_1820_);
v___x_1855_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1856_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1855_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1856_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_del_object(v___x_1825_);
lean_dec_ref(v_k_1823_);
lean_dec(v_i_1821_);
lean_dec(v_fvarId_1820_);
v_a_1857_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1827_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1827_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1866_; lean_object* v_i_1867_; lean_object* v_offset_1868_; lean_object* v_y_1869_; lean_object* v_ty_1870_; lean_object* v_k_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1914_; 
v_fvarId_1866_ = lean_ctor_get(v_c_1611_, 0);
v_i_1867_ = lean_ctor_get(v_c_1611_, 1);
v_offset_1868_ = lean_ctor_get(v_c_1611_, 2);
v_y_1869_ = lean_ctor_get(v_c_1611_, 3);
v_ty_1870_ = lean_ctor_get(v_c_1611_, 4);
v_k_1871_ = lean_ctor_get(v_c_1611_, 5);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1873_ = v_c_1611_;
v_isShared_1874_ = v_isSharedCheck_1914_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_k_1871_);
lean_inc(v_ty_1870_);
lean_inc(v_y_1869_);
lean_inc(v_offset_1868_);
lean_inc(v_i_1867_);
lean_inc(v_fvarId_1866_);
lean_dec(v_c_1611_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1914_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1869_, v_a_1612_);
lean_dec(v_y_1869_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
if (lean_obj_tag(v_a_1876_) == 0)
{
lean_object* v_id_1877_; lean_object* v___x_1878_; 
v_id_1877_ = lean_ctor_get(v_a_1876_, 0);
lean_inc(v_id_1877_);
lean_dec_ref_known(v_a_1876_, 1);
v___x_1878_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1866_, v_a_1612_);
lean_dec(v_fvarId_1866_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
if (lean_obj_tag(v_a_1879_) == 0)
{
lean_object* v_id_1880_; lean_object* v___x_1881_; 
v_id_1880_ = lean_ctor_get(v_a_1879_, 0);
lean_inc(v_id_1880_);
lean_dec_ref_known(v_a_1879_, 1);
v___x_1881_ = l_Lean_IR_ToIR_lowerCode(v_k_1871_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1893_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1893_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1893_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = l_Lean_IR_toIRType(v_ty_1870_);
lean_dec_ref(v_ty_1870_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 23);
lean_ctor_set(v___x_1873_, 5, v_a_1882_);
lean_ctor_set(v___x_1873_, 4, v___x_1886_);
lean_ctor_set(v___x_1873_, 3, v_id_1877_);
lean_ctor_set(v___x_1873_, 0, v_id_1880_);
v___x_1888_ = v___x_1873_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_id_1880_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_i_1867_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_offset_1868_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_id_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1892_, 5, v_a_1882_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1888_);
v___x_1890_ = v___x_1884_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_dec(v_id_1880_);
lean_dec(v_id_1877_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_ty_1870_);
lean_dec(v_offset_1868_);
lean_dec(v_i_1867_);
return v___x_1881_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_a_1879_);
lean_dec(v_id_1877_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_k_1871_);
lean_dec_ref(v_ty_1870_);
lean_dec(v_offset_1868_);
lean_dec(v_i_1867_);
v___x_1894_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1895_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1894_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1895_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_id_1877_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_k_1871_);
lean_dec_ref(v_ty_1870_);
lean_dec(v_offset_1868_);
lean_dec(v_i_1867_);
v_a_1896_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1878_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1878_);
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
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec(v_a_1876_);
lean_del_object(v___x_1873_);
lean_dec_ref(v_k_1871_);
lean_dec_ref(v_ty_1870_);
lean_dec(v_offset_1868_);
lean_dec(v_i_1867_);
lean_dec(v_fvarId_1866_);
v___x_1904_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1905_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1904_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1905_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1873_);
lean_dec_ref(v_k_1871_);
lean_dec_ref(v_ty_1870_);
lean_dec(v_offset_1868_);
lean_dec(v_i_1867_);
lean_dec(v_fvarId_1866_);
v_a_1906_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1875_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1875_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1915_; lean_object* v_cidx_1916_; lean_object* v_k_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1946_; 
v_fvarId_1915_ = lean_ctor_get(v_c_1611_, 0);
v_cidx_1916_ = lean_ctor_get(v_c_1611_, 1);
v_k_1917_ = lean_ctor_get(v_c_1611_, 2);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1919_ = v_c_1611_;
v_isShared_1920_ = v_isSharedCheck_1946_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_k_1917_);
lean_inc(v_cidx_1916_);
lean_inc(v_fvarId_1915_);
lean_dec(v_c_1611_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1946_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1915_, v_a_1612_);
lean_dec(v_fvarId_1915_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
if (lean_obj_tag(v_a_1922_) == 0)
{
lean_object* v_id_1923_; lean_object* v___x_1924_; 
v_id_1923_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_id_1923_);
lean_dec_ref_known(v_a_1922_, 1);
v___x_1924_ = l_Lean_IR_ToIR_lowerCode(v_k_1917_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1935_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1935_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1935_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 21);
lean_ctor_set(v___x_1919_, 2, v_a_1925_);
lean_ctor_set(v___x_1919_, 0, v_id_1923_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_id_1923_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_cidx_1916_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1930_);
v___x_1932_ = v___x_1927_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_dec(v_id_1923_);
lean_del_object(v___x_1919_);
lean_dec(v_cidx_1916_);
return v___x_1924_;
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_a_1922_);
lean_del_object(v___x_1919_);
lean_dec_ref(v_k_1917_);
lean_dec(v_cidx_1916_);
v___x_1936_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1937_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1936_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1937_;
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_del_object(v___x_1919_);
lean_dec_ref(v_k_1917_);
lean_dec(v_cidx_1916_);
v_a_1938_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1921_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1921_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1947_; lean_object* v_n_1948_; uint8_t v_check_1949_; uint8_t v_persistent_1950_; lean_object* v_k_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1980_; 
v_fvarId_1947_ = lean_ctor_get(v_c_1611_, 0);
v_n_1948_ = lean_ctor_get(v_c_1611_, 1);
v_check_1949_ = lean_ctor_get_uint8(v_c_1611_, sizeof(void*)*3);
v_persistent_1950_ = lean_ctor_get_uint8(v_c_1611_, sizeof(void*)*3 + 1);
v_k_1951_ = lean_ctor_get(v_c_1611_, 2);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1953_ = v_c_1611_;
v_isShared_1954_ = v_isSharedCheck_1980_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_k_1951_);
lean_inc(v_n_1948_);
lean_inc(v_fvarId_1947_);
lean_dec(v_c_1611_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1980_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1947_, v_a_1612_);
lean_dec(v_fvarId_1947_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
if (lean_obj_tag(v_a_1956_) == 0)
{
lean_object* v_id_1957_; lean_object* v___x_1958_; 
v_id_1957_ = lean_ctor_get(v_a_1956_, 0);
lean_inc(v_id_1957_);
lean_dec_ref_known(v_a_1956_, 1);
v___x_1958_ = l_Lean_IR_ToIR_lowerCode(v_k_1951_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1969_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 24);
lean_ctor_set(v___x_1953_, 2, v_a_1959_);
lean_ctor_set(v___x_1953_, 0, v_id_1957_);
v___x_1964_ = v___x_1953_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(24, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_id_1957_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_n_1948_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_a_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*3, v_check_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*3 + 1, v_persistent_1950_);
v___x_1964_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_dec(v_id_1957_);
lean_del_object(v___x_1953_);
lean_dec(v_n_1948_);
return v___x_1958_;
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_a_1956_);
lean_del_object(v___x_1953_);
lean_dec_ref(v_k_1951_);
lean_dec(v_n_1948_);
v___x_1970_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1971_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1970_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1971_;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1953_);
lean_dec_ref(v_k_1951_);
lean_dec(v_n_1948_);
v_a_1972_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1955_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1955_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1981_; lean_object* v_n_1982_; uint8_t v_check_1983_; uint8_t v_persistent_1984_; lean_object* v_k_1985_; lean_object* v___x_1986_; 
v_fvarId_1981_ = lean_ctor_get(v_c_1611_, 0);
lean_inc(v_fvarId_1981_);
v_n_1982_ = lean_ctor_get(v_c_1611_, 1);
lean_inc(v_n_1982_);
v_check_1983_ = lean_ctor_get_uint8(v_c_1611_, sizeof(void*)*4);
v_persistent_1984_ = lean_ctor_get_uint8(v_c_1611_, sizeof(void*)*4 + 1);
v_k_1985_ = lean_ctor_get(v_c_1611_, 3);
lean_inc_ref(v_k_1985_);
lean_dec_ref_known(v_c_1611_, 4);
v___x_1986_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1981_, v_a_1612_);
lean_dec(v_fvarId_1981_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
if (lean_obj_tag(v_a_1987_) == 0)
{
lean_object* v_id_1988_; lean_object* v___x_1989_; 
v_id_1988_ = lean_ctor_get(v_a_1987_, 0);
lean_inc(v_id_1988_);
lean_dec_ref_known(v_a_1987_, 1);
v___x_1989_ = l_Lean_IR_ToIR_lowerCode(v_k_1985_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1998_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_alloc_ctor(25, 3, 2);
lean_ctor_set(v___x_1994_, 0, v_id_1988_);
lean_ctor_set(v___x_1994_, 1, v_n_1982_);
lean_ctor_set(v___x_1994_, 2, v_a_1990_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*3, v_check_1983_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*3 + 1, v_persistent_1984_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
else
{
lean_dec(v_id_1988_);
lean_dec(v_n_1982_);
return v___x_1989_;
}
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec(v_a_1987_);
lean_dec_ref(v_k_1985_);
lean_dec(v_n_1982_);
v___x_1999_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_2000_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1999_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_2000_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_k_1985_);
lean_dec(v_n_1982_);
v_a_2001_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1986_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1986_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
default: 
{
lean_object* v_fvarId_2009_; lean_object* v_k_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2039_; 
v_fvarId_2009_ = lean_ctor_get(v_c_1611_, 0);
v_k_2010_ = lean_ctor_get(v_c_1611_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_c_1611_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2012_ = v_c_1611_;
v_isShared_2013_ = v_isSharedCheck_2039_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_k_2010_);
lean_inc(v_fvarId_2009_);
lean_dec(v_c_1611_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2039_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_2009_, v_a_1612_);
lean_dec(v_fvarId_2009_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
if (lean_obj_tag(v_a_2015_) == 0)
{
lean_object* v_id_2016_; lean_object* v___x_2017_; 
v_id_2016_ = lean_ctor_get(v_a_2015_, 0);
lean_inc(v_id_2016_);
lean_dec_ref_known(v_a_2015_, 1);
v___x_2017_ = l_Lean_IR_ToIR_lowerCode(v_k_2010_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2028_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2028_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2028_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 26);
lean_ctor_set(v___x_2012_, 1, v_a_2018_);
lean_ctor_set(v___x_2012_, 0, v_id_2016_);
v___x_2023_ = v___x_2012_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(26, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_id_2016_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2023_);
v___x_2025_ = v___x_2020_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_dec(v_id_2016_);
lean_del_object(v___x_2012_);
return v___x_2017_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v_a_2015_);
lean_del_object(v___x_2012_);
lean_dec_ref(v_k_2010_);
v___x_2029_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_2030_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_2029_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_2030_;
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_del_object(v___x_2012_);
lean_dec_ref(v_k_2010_);
v_a_2031_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2014_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2014_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_2040_, lean_object* v_k_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_fvarId_2046_; lean_object* v___x_2047_; 
v_fvarId_2046_ = lean_ctor_get(v_decl_2040_, 0);
lean_inc(v_fvarId_2046_);
lean_dec_ref(v_decl_2040_);
v___x_2047_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_2046_, v_a_2042_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref_known(v___x_2047_, 1);
v___x_2048_ = l_Lean_IR_ToIR_lowerCode(v_k_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_k_2041_);
v_a_2049_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2047_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_2057_, lean_object* v_k_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_2057_, v_k_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_2064_, lean_object* v_k_2065_, lean_object* v_fvarId_2066_, lean_object* v_f_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2064_, v_k_2065_, v_fvarId_2066_, v_f_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec(v_fvarId_2066_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_2073_, lean_object* v_i_2074_, lean_object* v_bs_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2073_);
lean_dec(v_sz_2073_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_2080_, v_i_boxed_2081_, v_bs_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_IR_ToIR_lowerAlt(v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_2089_, lean_object* v_k_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_IR_ToIR_lowerLet(v_decl_2089_, v_k_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_IR_ToIR_lowerCode(v_c_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_2102_, lean_object* v_k_2103_, lean_object* v_x_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_2102_, v_k_2103_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_2110_, lean_object* v_k_2111_, lean_object* v_x_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_2110_, v_k_2111_, v_x_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_2118_, size_t v_i_2119_, lean_object* v_bs_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_2118_, v_i_2119_, v_bs_2120_, v___y_2121_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_2126_, lean_object* v_i_2127_, lean_object* v_bs_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
size_t v_sz_boxed_2133_; size_t v_i_boxed_2134_; lean_object* v_res_2135_; 
v_sz_boxed_2133_ = lean_unbox_usize(v_sz_2126_);
lean_dec(v_sz_2126_);
v_i_boxed_2134_ = lean_unbox_usize(v_i_2127_);
lean_dec(v_i_2127_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_2133_, v_i_boxed_2134_, v_bs_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_2136_, size_t v_i_2137_, lean_object* v_bs_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2136_, v_i_2137_, v_bs_2138_, v___y_2139_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_2144_, lean_object* v_i_2145_, lean_object* v_bs_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
size_t v_sz_boxed_2151_; size_t v_i_boxed_2152_; lean_object* v_res_2153_; 
v_sz_boxed_2151_ = lean_unbox_usize(v_sz_2144_);
lean_dec(v_sz_2144_);
v_i_boxed_2152_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_2151_, v_i_boxed_2152_, v_bs_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_toSignature_2159_; lean_object* v_value_2160_; lean_object* v_name_2161_; lean_object* v_type_2162_; lean_object* v_params_2163_; size_t v_sz_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v_toSignature_2159_ = lean_ctor_get(v_d_2154_, 0);
lean_inc_ref(v_toSignature_2159_);
v_value_2160_ = lean_ctor_get(v_d_2154_, 1);
lean_inc_ref(v_value_2160_);
lean_dec_ref(v_d_2154_);
v_name_2161_ = lean_ctor_get(v_toSignature_2159_, 0);
lean_inc(v_name_2161_);
v_type_2162_ = lean_ctor_get(v_toSignature_2159_, 2);
lean_inc_ref(v_type_2162_);
v_params_2163_ = lean_ctor_get(v_toSignature_2159_, 3);
lean_inc_ref(v_params_2163_);
lean_dec_ref(v_toSignature_2159_);
v_sz_2164_ = lean_array_size(v_params_2163_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_2164_, v___x_2165_, v_params_2163_, v_a_2155_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2231_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2231_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2231_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_IR_toIRType(v_type_2162_);
lean_dec_ref(v_type_2162_);
if (lean_obj_tag(v_value_2160_) == 0)
{
lean_object* v_code_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2206_; 
lean_del_object(v___x_2169_);
v_code_2172_ = lean_ctor_get(v_value_2160_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_value_2160_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2174_ = v_value_2160_;
v_isShared_2175_ = v_isSharedCheck_2206_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_code_2172_);
lean_dec(v_value_2160_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2206_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_IR_ToIR_lowerCode(v_code_2172_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2197_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2197_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2197_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v_nextJpId_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_nextVarId_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2181_ = lean_st_ref_get(v_a_2155_);
v_nextJpId_2182_ = lean_ctor_get(v___x_2181_, 3);
lean_inc(v_nextJpId_2182_);
lean_dec(v___x_2181_);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_sub(v_nextJpId_2182_, v___x_2183_);
lean_dec(v_nextJpId_2182_);
v___x_2185_ = lean_st_ref_get(v_a_2155_);
v_nextVarId_2186_ = lean_ctor_get(v___x_2185_, 2);
lean_inc(v_nextVarId_2186_);
lean_dec(v___x_2185_);
v___x_2187_ = lean_nat_sub(v_nextVarId_2186_, v___x_2183_);
lean_dec(v_nextVarId_2186_);
v___x_2188_ = lean_box(0);
v___x_2189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2184_);
lean_ctor_set(v___x_2189_, 2, v___x_2187_);
v___x_2190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2190_, 0, v_name_2161_);
lean_ctor_set(v___x_2190_, 1, v_a_2167_);
lean_ctor_set(v___x_2190_, 2, v___x_2171_);
lean_ctor_set(v___x_2190_, 3, v_a_2177_);
lean_ctor_set(v___x_2190_, 4, v___x_2189_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 1);
lean_ctor_set(v___x_2174_, 0, v___x_2190_);
v___x_2192_ = v___x_2174_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2192_);
v___x_2194_ = v___x_2179_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2174_);
lean_dec(v___x_2171_);
lean_dec(v_a_2167_);
lean_dec(v_name_2161_);
v_a_2198_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2176_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2176_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2230_; 
v_externAttrData_2207_ = lean_ctor_get(v_value_2160_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_value_2160_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2209_ = v_value_2160_;
v_isShared_2210_ = v_isSharedCheck_2230_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_externAttrData_2207_);
lean_dec(v_value_2160_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2230_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
uint8_t v___x_2211_; 
v___x_2211_ = l_List_isEmpty___redArg(v_externAttrData_2207_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2212_, 0, v_name_2161_);
lean_ctor_set(v___x_2212_, 1, v_a_2167_);
lean_ctor_set(v___x_2212_, 2, v___x_2171_);
lean_ctor_set(v___x_2212_, 3, v_externAttrData_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2212_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2216_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2214_);
v___x_2216_ = v___x_2169_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
lean_del_object(v___x_2209_);
lean_dec(v_externAttrData_2207_);
lean_del_object(v___x_2169_);
v___x_2219_ = l_Lean_IR_mkDummyExternDecl(v_name_2161_, v_a_2167_, v___x_2171_);
v___x_2220_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_2219_, v_a_2157_);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2229_);
v___x_2222_ = v___x_2220_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v___x_2220_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_type_2162_);
lean_dec(v_name_2161_);
lean_dec_ref(v_value_2160_);
v_a_2232_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2166_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2166_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_IR_ToIR_lowerDecl(v_d_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_a_2254_; uint8_t v___x_2258_; 
v___x_2258_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_b_2249_);
return v___x_2259_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_a_2260_ = lean_array_uget_borrowed(v_as_2246_, v_i_2248_);
lean_inc(v_a_2260_);
v___x_2261_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_2261_, 0, v_a_2260_);
v___x_2262_ = l_Lean_IR_ToIR_M_run___redArg(v___x_2261_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
if (lean_obj_tag(v_a_2263_) == 1)
{
lean_object* v_val_2264_; lean_object* v___x_2265_; 
v_val_2264_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_val_2264_);
lean_dec_ref_known(v_a_2263_, 1);
v___x_2265_ = lean_array_push(v_b_2249_, v_val_2264_);
v_a_2254_ = v___x_2265_;
goto v___jp_2253_;
}
else
{
lean_dec(v_a_2263_);
v_a_2254_ = v_b_2249_;
goto v___jp_2253_;
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_b_2249_);
v_a_2266_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2262_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2262_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
v___jp_2253_:
{
size_t v___x_2255_; size_t v___x_2256_; 
v___x_2255_ = ((size_t)1ULL);
v___x_2256_ = lean_usize_add(v_i_2248_, v___x_2255_);
v_i_2248_ = v___x_2256_;
v_b_2249_ = v_a_2254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_2274_, lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
size_t v_sz_boxed_2281_; size_t v_i_boxed_2282_; lean_object* v_res_2283_; 
v_sz_boxed_2281_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2282_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_2274_, v_sz_boxed_2281_, v_i_boxed_2282_, v_b_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2274_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_irDecls_2290_; size_t v_sz_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v_irDecls_2290_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_2291_ = lean_array_size(v_decls_2286_);
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_2286_, v_sz_2291_, v___x_2292_, v_irDecls_2290_, v_a_2287_, v_a_2288_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_IR_toIR(v_decls_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec_ref(v_decls_2294_);
return v_res_2298_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
