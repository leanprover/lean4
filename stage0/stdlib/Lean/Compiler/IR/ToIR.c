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
extern lean_object* l_Lean_IR_instInhabitedArg_default;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2));
v___x_47_ = lean_unsigned_to_nat(11u);
v___x_48_ = lean_unsigned_to_nat(163u);
v___x_49_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1));
v___x_50_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0));
v___x_51_ = l_mkPanicMessageWithDecl(v___x_50_, v___x_49_, v___x_48_, v___x_47_, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object* v_inst_52_, lean_object* v_a_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3);
v___x_56_ = lean_panic_fn(v_inst_52_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_key_57_; lean_object* v_value_58_; lean_object* v_tail_59_; uint8_t v___x_60_; 
v_key_57_ = lean_ctor_get(v_x_54_, 0);
v_value_58_ = lean_ctor_get(v_x_54_, 1);
v_tail_59_ = lean_ctor_get(v_x_54_, 2);
v___x_60_ = l_Lean_instBEqFVarId_beq(v_key_57_, v_a_53_);
if (v___x_60_ == 0)
{
v_x_54_ = v_tail_59_;
goto _start;
}
else
{
lean_dec(v_inst_52_);
lean_inc(v_value_58_);
return v_value_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_inst_62_, lean_object* v_a_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_inst_62_, v_a_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object* v_inst_66_, lean_object* v_m_67_, lean_object* v_a_68_){
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
v___x_84_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_inst_66_, v_a_68_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object* v_inst_85_, lean_object* v_m_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(v_inst_85_, v_m_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_m_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* v_fvarId_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_vars_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = lean_st_ref_get(v_a_90_);
v_vars_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_vars_93_);
lean_dec(v___x_92_);
v___x_94_ = l_Lean_IR_instInhabitedArg_default;
v___x_95_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(v___x_94_, v_vars_93_, v_fvarId_89_);
lean_dec_ref(v_vars_93_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* v_fvarId_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec(v_fvarId_97_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* v_fvarId_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_101_, v_a_102_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* v_fvarId_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_IR_ToIR_getFVarValue(v_fvarId_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec(v_fvarId_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object* v_00_u03b2_113_, lean_object* v_inst_114_, lean_object* v_m_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(v_inst_114_, v_m_115_, v_a_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* v_00_u03b2_118_, lean_object* v_inst_119_, lean_object* v_m_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_00_u03b2_118_, v_inst_119_, v_m_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_m_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object* v_inst_123_, lean_object* v_msg_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_panic_fn(v_inst_123_, v_msg_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_msg_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_panic_fn(v_inst_127_, v_msg_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* v_00_u03b2_130_, lean_object* v_inst_131_, lean_object* v_a_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_inst_131_, v_a_132_, v_x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_135_, lean_object* v_inst_136_, lean_object* v_a_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_00_u03b2_135_, v_inst_136_, v_a_137_, v_x_138_);
lean_dec(v_x_138_);
lean_dec(v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* v_fvarId_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_joinPoints_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = lean_st_ref_get(v_a_141_);
v_joinPoints_144_ = lean_ctor_get(v___x_143_, 1);
lean_inc_ref(v_joinPoints_144_);
lean_dec(v___x_143_);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(v___x_145_, v_joinPoints_144_, v_fvarId_140_);
lean_dec_ref(v_joinPoints_144_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* v_fvarId_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec(v_fvarId_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* v_fvarId_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_152_, v_a_153_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* v_fvarId_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_IR_ToIR_getJoinPointValue(v_fvarId_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec(v_fvarId_158_);
return v_res_163_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
lean_object* v_key_167_; lean_object* v_tail_168_; uint8_t v___x_169_; 
v_key_167_ = lean_ctor_get(v_x_165_, 0);
v_tail_168_ = lean_ctor_get(v_x_165_, 2);
v___x_169_ = l_Lean_instBEqFVarId_beq(v_key_167_, v_a_164_);
if (v___x_169_ == 0)
{
v_x_165_ = v_tail_168_;
goto _start;
}
else
{
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_171_, v_x_172_);
lean_dec(v_x_172_);
lean_dec(v_a_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
return v_x_175_;
}
else
{
lean_object* v_key_177_; lean_object* v_value_178_; lean_object* v_tail_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_202_; 
v_key_177_ = lean_ctor_get(v_x_176_, 0);
v_value_178_ = lean_ctor_get(v_x_176_, 1);
v_tail_179_ = lean_ctor_get(v_x_176_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_x_176_);
if (v_isSharedCheck_202_ == 0)
{
v___x_181_ = v_x_176_;
v_isShared_182_ = v_isSharedCheck_202_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_tail_179_);
lean_inc(v_value_178_);
lean_inc(v_key_177_);
lean_dec(v_x_176_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_202_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v_fold_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_183_ = lean_array_get_size(v_x_175_);
v___x_184_ = l_Lean_instHashableFVarId_hash(v_key_177_);
v___x_185_ = 32ULL;
v___x_186_ = lean_uint64_shift_right(v___x_184_, v___x_185_);
v_fold_187_ = lean_uint64_xor(v___x_184_, v___x_186_);
v___x_188_ = 16ULL;
v___x_189_ = lean_uint64_shift_right(v_fold_187_, v___x_188_);
v___x_190_ = lean_uint64_xor(v_fold_187_, v___x_189_);
v___x_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = lean_usize_of_nat(v___x_183_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_sub(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_land(v___x_191_, v___x_194_);
v___x_196_ = lean_array_uget_borrowed(v_x_175_, v___x_195_);
lean_inc(v___x_196_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v___x_196_);
v___x_198_ = v___x_181_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_key_177_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_value_178_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___x_196_);
v___x_198_ = v_reuseFailAlloc_201_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = lean_array_uset(v_x_175_, v___x_195_, v___x_198_);
v_x_175_ = v___x_199_;
v_x_176_ = v_tail_179_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_203_, lean_object* v_source_204_, lean_object* v_target_205_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_array_get_size(v_source_204_);
v___x_207_ = lean_nat_dec_lt(v_i_203_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec_ref(v_source_204_);
lean_dec(v_i_203_);
return v_target_205_;
}
else
{
lean_object* v_es_208_; lean_object* v___x_209_; lean_object* v_source_210_; lean_object* v_target_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_es_208_ = lean_array_fget(v_source_204_, v_i_203_);
v___x_209_ = lean_box(0);
v_source_210_ = lean_array_fset(v_source_204_, v_i_203_, v___x_209_);
v_target_211_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_205_, v_es_208_);
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v_i_203_, v___x_212_);
lean_dec(v_i_203_);
v_i_203_ = v___x_213_;
v_source_204_ = v_source_210_;
v_target_205_ = v_target_211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object* v_data_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_nbuckets_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_216_ = lean_array_get_size(v_data_215_);
v___x_217_ = lean_unsigned_to_nat(2u);
v_nbuckets_218_ = lean_nat_mul(v___x_216_, v___x_217_);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_box(0);
v___x_221_ = lean_mk_array(v_nbuckets_218_, v___x_220_);
v___x_222_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v___x_219_, v_data_215_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* v_m_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
lean_object* v_size_226_; lean_object* v_buckets_227_; lean_object* v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v_fold_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v_bkt_241_; uint8_t v___x_242_; 
v_size_226_ = lean_ctor_get(v_m_223_, 0);
v_buckets_227_ = lean_ctor_get(v_m_223_, 1);
v___x_228_ = lean_array_get_size(v_buckets_227_);
v___x_229_ = l_Lean_instHashableFVarId_hash(v_a_224_);
v___x_230_ = 32ULL;
v___x_231_ = lean_uint64_shift_right(v___x_229_, v___x_230_);
v_fold_232_ = lean_uint64_xor(v___x_229_, v___x_231_);
v___x_233_ = 16ULL;
v___x_234_ = lean_uint64_shift_right(v_fold_232_, v___x_233_);
v___x_235_ = lean_uint64_xor(v_fold_232_, v___x_234_);
v___x_236_ = lean_uint64_to_usize(v___x_235_);
v___x_237_ = lean_usize_of_nat(v___x_228_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_sub(v___x_237_, v___x_238_);
v___x_240_ = lean_usize_land(v___x_236_, v___x_239_);
v_bkt_241_ = lean_array_uget_borrowed(v_buckets_227_, v___x_240_);
v___x_242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_224_, v_bkt_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_263_; 
lean_inc_ref(v_buckets_227_);
lean_inc(v_size_226_);
v_isSharedCheck_263_ = !lean_is_exclusive(v_m_223_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; 
v_unused_264_ = lean_ctor_get(v_m_223_, 1);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_m_223_, 0);
lean_dec(v_unused_265_);
v___x_244_ = v_m_223_;
v_isShared_245_ = v_isSharedCheck_263_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_m_223_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_263_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v_size_x27_247_; lean_object* v___x_248_; lean_object* v_buckets_x27_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v_size_x27_247_ = lean_nat_add(v_size_226_, v___x_246_);
lean_dec(v_size_226_);
lean_inc(v_bkt_241_);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v_a_224_);
lean_ctor_set(v___x_248_, 1, v_b_225_);
lean_ctor_set(v___x_248_, 2, v_bkt_241_);
v_buckets_x27_249_ = lean_array_uset(v_buckets_227_, v___x_240_, v___x_248_);
v___x_250_ = lean_unsigned_to_nat(4u);
v___x_251_ = lean_nat_mul(v_size_x27_247_, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(3u);
v___x_253_ = lean_nat_div(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_array_get_size(v_buckets_x27_249_);
v___x_255_ = lean_nat_dec_le(v___x_253_, v___x_254_);
lean_dec(v___x_253_);
if (v___x_255_ == 0)
{
lean_object* v_val_256_; lean_object* v___x_258_; 
v_val_256_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_buckets_x27_249_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v_val_256_);
lean_ctor_set(v___x_244_, 0, v_size_x27_247_);
v___x_258_ = v___x_244_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_size_x27_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_val_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
lean_object* v___x_261_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v_buckets_x27_249_);
lean_ctor_set(v___x_244_, 0, v_size_x27_247_);
v___x_261_ = v___x_244_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_size_x27_247_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_buckets_x27_249_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_dec(v_b_225_);
lean_dec(v_a_224_);
return v_m_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* v_fvarId_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_vars_270_; lean_object* v_joinPoints_271_; lean_object* v_nextId_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_285_; 
v___x_269_ = lean_st_ref_take(v_a_267_);
v_vars_270_ = lean_ctor_get(v___x_269_, 0);
v_joinPoints_271_ = lean_ctor_get(v___x_269_, 1);
v_nextId_272_ = lean_ctor_get(v___x_269_, 2);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_285_ == 0)
{
v___x_274_ = v___x_269_;
v_isShared_275_ = v_isSharedCheck_285_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_nextId_272_);
lean_inc(v_joinPoints_271_);
lean_inc(v_vars_270_);
lean_dec(v___x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_285_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_inc(v_nextId_272_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_nextId_272_);
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_270_, v_fvarId_266_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_nextId_272_, v___x_278_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 2, v___x_279_);
lean_ctor_set(v___x_274_, 0, v___x_277_);
v___x_281_ = v___x_274_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_joinPoints_271_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v___x_279_);
v___x_281_ = v_reuseFailAlloc_284_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_st_ref_set(v_a_267_, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_nextId_272_);
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_286_, v_a_287_);
lean_dec(v_a_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_290_, v_a_291_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_IR_ToIR_bindVar(v_fvarId_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_302_, lean_object* v_m_303_, lean_object* v_a_304_, lean_object* v_b_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_303_, v_a_304_, v_b_305_);
return v___x_306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_307_, lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_308_, v_x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_311_, v_a_312_, v_x_313_);
lean_dec(v_x_313_);
lean_dec(v_a_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* v_00_u03b2_316_, lean_object* v_data_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_319_, lean_object* v_i_320_, lean_object* v_source_321_, lean_object* v_target_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_320_, v_source_321_, v_target_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_325_, v_x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; lean_object* v_vars_332_; lean_object* v_joinPoints_333_; lean_object* v_nextId_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_346_; 
v___x_331_ = lean_st_ref_take(v_a_329_);
v_vars_332_ = lean_ctor_get(v___x_331_, 0);
v_joinPoints_333_ = lean_ctor_get(v___x_331_, 1);
v_nextId_334_ = lean_ctor_get(v___x_331_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_346_ == 0)
{
v___x_336_ = v___x_331_;
v_isShared_337_ = v_isSharedCheck_346_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_nextId_334_);
lean_inc(v_joinPoints_333_);
lean_inc(v_vars_332_);
lean_dec(v___x_331_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_346_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
lean_inc(v_nextId_334_);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_333_, v_fvarId_328_, v_nextId_334_);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_nextId_334_, v___x_339_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 2, v___x_340_);
lean_ctor_set(v___x_336_, 1, v___x_338_);
v___x_342_ = v___x_336_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_vars_332_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v___x_340_);
v___x_342_ = v_reuseFailAlloc_345_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_st_ref_set(v_a_329_, v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_nextId_334_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_347_, v_a_348_);
lean_dec(v_a_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_351_, v_a_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; lean_object* v_vars_367_; lean_object* v_joinPoints_368_; lean_object* v_nextId_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
v___x_366_ = lean_st_ref_take(v_a_364_);
v_vars_367_ = lean_ctor_get(v___x_366_, 0);
v_joinPoints_368_ = lean_ctor_get(v___x_366_, 1);
v_nextId_369_ = lean_ctor_get(v___x_366_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_371_ = v___x_366_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_nextId_369_);
lean_inc(v_joinPoints_368_);
lean_inc(v_vars_367_);
lean_dec(v___x_366_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_box(1);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_367_, v_fvarId_363_, v___x_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_joinPoints_368_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_nextId_369_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_st_ref_set(v_a_364_, v___x_376_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_382_, v_a_383_);
lean_dec(v_a_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_386_, v_a_387_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_IR_ToIR_bindErased(v_fvarId_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_398_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v_env_407_; lean_object* v_nextMacroScope_408_; lean_object* v_ngen_409_; lean_object* v_auxDeclNGen_410_; lean_object* v_traceState_411_; lean_object* v_messages_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_430_; 
v___x_406_ = lean_st_ref_take(v_a_404_);
v_env_407_ = lean_ctor_get(v___x_406_, 0);
v_nextMacroScope_408_ = lean_ctor_get(v___x_406_, 1);
v_ngen_409_ = lean_ctor_get(v___x_406_, 2);
v_auxDeclNGen_410_ = lean_ctor_get(v___x_406_, 3);
v_traceState_411_ = lean_ctor_get(v___x_406_, 4);
v_messages_412_ = lean_ctor_get(v___x_406_, 6);
v_infoState_413_ = lean_ctor_get(v___x_406_, 7);
v_snapshotTasks_414_ = lean_ctor_get(v___x_406_, 8);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_406_, 5);
lean_dec(v_unused_431_);
v___x_416_ = v___x_406_;
v_isShared_417_ = v_isSharedCheck_430_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snapshotTasks_414_);
lean_inc(v_infoState_413_);
lean_inc(v_messages_412_);
lean_inc(v_traceState_411_);
lean_inc(v_auxDeclNGen_410_);
lean_inc(v_ngen_409_);
lean_inc(v_nextMacroScope_408_);
lean_inc(v_env_407_);
lean_dec(v___x_406_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_430_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_toEnvExtension_419_; lean_object* v_asyncMode_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_418_ = l_Lean_IR_declMapExt;
v_toEnvExtension_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_toEnvExtension_419_);
v_asyncMode_420_ = lean_ctor_get(v_toEnvExtension_419_, 2);
lean_inc(v_asyncMode_420_);
lean_dec_ref(v_toEnvExtension_419_);
v___x_421_ = lean_box(0);
v___x_422_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_418_, v_env_407_, v_d_403_, v_asyncMode_420_, v___x_421_);
lean_dec(v_asyncMode_420_);
v___x_423_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 5, v___x_423_);
lean_ctor_set(v___x_416_, 0, v___x_422_);
v___x_425_ = v___x_416_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_nextMacroScope_408_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_ngen_409_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_auxDeclNGen_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_traceState_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v_messages_412_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v_infoState_413_);
lean_ctor_set(v_reuseFailAlloc_429_, 8, v_snapshotTasks_414_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_st_ref_set(v_a_404_, v___x_425_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_432_, v_a_433_);
lean_dec(v_a_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_436_, v_a_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_IR_ToIR_addDecl(v_d_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_448_){
_start:
{
switch(lean_obj_tag(v_v_448_))
{
case 0:
{
lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_463_; 
v_val_449_ = lean_ctor_get(v_v_448_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_v_448_);
if (v_isSharedCheck_463_ == 0)
{
v___x_451_ = v_v_448_;
v_isShared_452_ = v_isSharedCheck_463_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v_v_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_463_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___y_454_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_cstr_to_nat("4294967296");
v___x_460_ = lean_nat_dec_lt(v_val_449_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
v___x_461_ = lean_box(8);
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(12);
v___y_454_ = v___x_462_;
goto v___jp_453_;
}
v___jp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_452_ == 0)
{
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_val_449_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___y_454_);
return v___x_457_;
}
}
}
}
case 1:
{
lean_object* v_val_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_473_; 
v_val_464_ = lean_ctor_get(v_v_448_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_v_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_466_ = v_v_448_;
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_val_464_);
lean_dec(v_v_448_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_val_464_);
v___x_469_ = v_reuseFailAlloc_472_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_box(7);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
}
case 2:
{
uint8_t v_val_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_val_474_ = lean_ctor_get_uint8(v_v_448_, 0);
lean_dec_ref(v_v_448_);
v___x_475_ = lean_uint8_to_nat(v_val_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = lean_box(1);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
case 3:
{
uint16_t v_val_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_val_479_ = lean_ctor_get_uint16(v_v_448_, 0);
lean_dec_ref(v_v_448_);
v___x_480_ = lean_uint16_to_nat(v_val_479_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
v___x_482_ = lean_box(2);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
return v___x_483_;
}
case 4:
{
uint32_t v_val_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_val_484_ = lean_ctor_get_uint32(v_v_448_, 0);
lean_dec_ref(v_v_448_);
v___x_485_ = lean_uint32_to_nat(v_val_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
v___x_487_ = lean_box(3);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
case 5:
{
uint64_t v_val_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_val_489_ = lean_ctor_get_uint64(v_v_448_, 0);
lean_dec_ref(v_v_448_);
v___x_490_ = lean_uint64_to_nat(v_val_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
v___x_492_ = lean_box(4);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
return v___x_493_;
}
default: 
{
uint64_t v_val_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_val_494_ = lean_ctor_get_uint64(v_v_448_, 0);
lean_dec_ref(v_v_448_);
v___x_495_ = lean_uint64_to_nat(v_val_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___x_497_ = lean_box(5);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(1);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_fvarId_504_; lean_object* v___x_505_; 
v_fvarId_504_ = lean_ctor_get(v_a_499_, 0);
v___x_505_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_504_, v_a_500_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_510_, v_a_511_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_IR_ToIR_lowerArg(v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_fvarId_525_; lean_object* v_type_526_; uint8_t v_borrow_527_; lean_object* v___x_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_538_; 
v_fvarId_525_ = lean_ctor_get(v_p_522_, 0);
lean_inc(v_fvarId_525_);
v_type_526_ = lean_ctor_get(v_p_522_, 2);
lean_inc_ref(v_type_526_);
v_borrow_527_ = lean_ctor_get_uint8(v_p_522_, sizeof(void*)*3);
lean_dec_ref(v_p_522_);
v___x_528_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_525_, v_a_523_);
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_538_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = l_Lean_IR_toIRType(v_type_526_);
lean_dec_ref(v_type_526_);
v___x_534_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_534_, 0, v_a_529_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*2, v_borrow_527_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_534_);
v___x_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_539_, v_a_540_);
lean_dec(v_a_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_543_, v_a_544_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_IR_ToIR_lowerParam(v_p_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_555_){
_start:
{
lean_object* v_name_556_; lean_object* v_cidx_557_; lean_object* v_size_558_; lean_object* v_usize_559_; lean_object* v_ssize_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_name_556_ = lean_ctor_get(v_i_555_, 0);
v_cidx_557_ = lean_ctor_get(v_i_555_, 1);
v_size_558_ = lean_ctor_get(v_i_555_, 2);
v_usize_559_ = lean_ctor_get(v_i_555_, 3);
v_ssize_560_ = lean_ctor_get(v_i_555_, 4);
v_isSharedCheck_567_ = !lean_is_exclusive(v_i_555_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v_i_555_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_ssize_560_);
lean_inc(v_usize_559_);
lean_inc(v_size_558_);
lean_inc(v_cidx_557_);
lean_inc(v_name_556_);
lean_dec(v_i_555_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_name_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_cidx_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_size_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_usize_559_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_ssize_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_instMonadEIO(lean_box(0));
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_toApplicative_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_610_; 
v___x_576_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_577_ = l_StateRefT_x27_instMonad___redArg(v___x_576_);
v_toApplicative_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_577_, 1);
lean_dec(v_unused_611_);
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_610_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_toApplicative_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_610_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_toFunctor_582_; lean_object* v_toSeq_583_; lean_object* v_toSeqLeft_584_; lean_object* v_toSeqRight_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_608_; 
v_toFunctor_582_ = lean_ctor_get(v_toApplicative_578_, 0);
v_toSeq_583_ = lean_ctor_get(v_toApplicative_578_, 2);
v_toSeqLeft_584_ = lean_ctor_get(v_toApplicative_578_, 3);
v_toSeqRight_585_ = lean_ctor_get(v_toApplicative_578_, 4);
v_isSharedCheck_608_ = !lean_is_exclusive(v_toApplicative_578_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v_toApplicative_578_, 1);
lean_dec(v_unused_609_);
v___x_587_ = v_toApplicative_578_;
v_isShared_588_ = v_isSharedCheck_608_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_toSeqRight_585_);
lean_inc(v_toSeqLeft_584_);
lean_inc(v_toSeq_583_);
lean_inc(v_toFunctor_582_);
lean_dec(v_toApplicative_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_608_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_598_; 
v___f_589_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_590_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_582_);
v___f_591_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_591_, 0, v_toFunctor_582_);
v___f_592_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_592_, 0, v_toFunctor_582_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___f_591_);
lean_ctor_set(v___x_593_, 1, v___f_592_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_594_, 0, v_toSeqRight_585_);
v___f_595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_595_, 0, v_toSeqLeft_584_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_596_, 0, v_toSeq_583_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v___f_594_);
lean_ctor_set(v___x_587_, 3, v___f_595_);
lean_ctor_set(v___x_587_, 2, v___f_596_);
lean_ctor_set(v___x_587_, 1, v___f_589_);
lean_ctor_set(v___x_587_, 0, v___x_593_);
v___x_598_ = v___x_587_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___f_589_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___f_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v___f_595_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v___f_594_);
v___x_598_ = v_reuseFailAlloc_607_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___f_590_);
lean_ctor_set(v___x_580_, 0, v___x_598_);
v___x_600_ = v___x_580_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___f_590_);
v___x_600_ = v_reuseFailAlloc_606_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_8612__overap_604_; lean_object* v___x_605_; 
v___x_601_ = l_StateRefT_x27_instMonad___redArg(v___x_600_);
v___x_602_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_603_ = l_instInhabitedOfMonad___redArg(v___x_601_, v___x_602_);
v___x_8612__overap_604_ = lean_panic_fn(v___x_603_, v_msg_571_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
v___x_605_ = lean_apply_4(v___x_8612__overap_604_, v___y_572_, v___y_573_, v___y_574_, lean_box(0));
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_618_, size_t v_i_619_, lean_object* v_bs_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_bs_620_);
return v___x_624_;
}
else
{
lean_object* v_v_625_; lean_object* v___x_626_; 
v_v_625_ = lean_array_uget_borrowed(v_bs_620_, v_i_619_);
v___x_626_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_625_, v___y_621_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref(v___x_626_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_620_, v_i_619_, v___x_628_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_619_, v___x_630_);
v___x_632_ = lean_array_uset(v_bs_x27_629_, v_i_619_, v_a_627_);
v_i_619_ = v___x_631_;
v_bs_620_ = v___x_632_;
goto _start;
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_bs_620_);
v_a_634_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_626_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_626_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_642_, lean_object* v_i_643_, lean_object* v_bs_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
size_t v_sz_boxed_647_; size_t v_i_boxed_648_; lean_object* v_res_649_; 
v_sz_boxed_647_ = lean_unbox_usize(v_sz_642_);
lean_dec(v_sz_642_);
v_i_boxed_648_ = lean_unbox_usize(v_i_643_);
lean_dec(v_i_643_);
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_647_, v_i_boxed_648_, v_bs_644_, v___y_645_);
lean_dec(v___y_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_650_, size_t v_i_651_, lean_object* v_bs_652_, lean_object* v___y_653_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_651_, v_sz_650_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_bs_652_);
return v___x_656_;
}
else
{
lean_object* v_v_657_; lean_object* v___x_658_; 
v_v_657_ = lean_array_uget_borrowed(v_bs_652_, v_i_651_);
lean_inc(v_v_657_);
v___x_658_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_657_, v___y_653_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; lean_object* v_bs_x27_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v___x_660_ = lean_unsigned_to_nat(0u);
v_bs_x27_661_ = lean_array_uset(v_bs_652_, v_i_651_, v___x_660_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_651_, v___x_662_);
v___x_664_ = lean_array_uset(v_bs_x27_661_, v_i_651_, v_a_659_);
v_i_651_ = v___x_663_;
v_bs_652_ = v___x_664_;
goto _start;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_bs_652_);
v_a_666_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_658_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_658_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_bs_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
size_t v_sz_boxed_679_; size_t v_i_boxed_680_; lean_object* v_res_681_; 
v_sz_boxed_679_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_680_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_679_, v_i_boxed_680_, v_bs_676_, v___y_677_);
lean_dec(v___y_677_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_682_, lean_object* v_continueLet_683_, lean_object* v_var_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_689_, 0, v_i_682_);
lean_ctor_set(v___x_689_, 1, v_var_684_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
v___x_690_ = lean_apply_5(v_continueLet_683_, v___x_689_, v___y_685_, v___y_686_, v___y_687_, lean_box(0));
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_691_, lean_object* v_continueLet_692_, lean_object* v_var_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_691_, v_continueLet_692_, v_var_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_699_, lean_object* v_offset_700_, lean_object* v_continueLet_701_, lean_object* v_var_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_707_, 0, v_n_699_);
lean_ctor_set(v___x_707_, 1, v_offset_700_);
lean_ctor_set(v___x_707_, 2, v_var_702_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
v___x_708_ = lean_apply_5(v_continueLet_701_, v___x_707_, v___y_703_, v___y_704_, v___y_705_, lean_box(0));
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_709_, lean_object* v_offset_710_, lean_object* v_continueLet_711_, lean_object* v_var_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_709_, v_offset_710_, v_continueLet_711_, v_var_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_718_, lean_object* v_continueLet_719_, lean_object* v_var_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_725_, 0, v_n_718_);
lean_ctor_set(v___x_725_, 1, v_var_720_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
v___x_726_ = lean_apply_5(v_continueLet_719_, v___x_725_, v___y_721_, v___y_722_, v___y_723_, lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_727_, lean_object* v_continueLet_728_, lean_object* v_var_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_727_, v_continueLet_728_, v_var_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_735_, lean_object* v_var_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_741_, 0, v_var_736_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
v___x_742_ = lean_apply_5(v_continueLet_735_, v___x_741_, v___y_737_, v___y_738_, v___y_739_, lean_box(0));
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_743_, lean_object* v_var_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_743_, v_var_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_750_, lean_object* v_continueLet_751_, lean_object* v_var_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_757_, 0, v_i_750_);
lean_ctor_set(v___x_757_, 1, v_var_752_);
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
lean_inc(v___y_753_);
v___x_758_ = lean_apply_5(v_continueLet_751_, v___x_757_, v___y_753_, v___y_754_, v___y_755_, lean_box(0));
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_759_, lean_object* v_continueLet_760_, lean_object* v_var_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_759_, v_continueLet_760_, v_var_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_767_, lean_object* v_continueLet_768_, lean_object* v_var_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = l_Lean_IR_toIRType(v_ty_767_);
v___x_775_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_var_769_);
lean_inc(v___y_772_);
lean_inc_ref(v___y_771_);
lean_inc(v___y_770_);
v___x_776_ = lean_apply_5(v_continueLet_768_, v___x_775_, v___y_770_, v___y_771_, v___y_772_, lean_box(0));
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_777_, lean_object* v_continueLet_778_, lean_object* v_var_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_777_, v_continueLet_778_, v_var_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v_ty_777_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_785_, lean_object* v_i_786_, uint8_t v_updateHeader_787_, lean_object* v_continueLet_788_, lean_object* v_var_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
size_t v_sz_794_; size_t v___x_795_; lean_object* v___x_796_; 
v_sz_794_ = lean_array_size(v_args_785_);
v___x_795_ = ((size_t)0ULL);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_794_, v___x_795_, v_args_785_, v___y_790_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_name_798_; lean_object* v_cidx_799_; lean_object* v_size_800_; lean_object* v_usize_801_; lean_object* v_ssize_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_811_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
v_name_798_ = lean_ctor_get(v_i_786_, 0);
v_cidx_799_ = lean_ctor_get(v_i_786_, 1);
v_size_800_ = lean_ctor_get(v_i_786_, 2);
v_usize_801_ = lean_ctor_get(v_i_786_, 3);
v_ssize_802_ = lean_ctor_get(v_i_786_, 4);
v_isSharedCheck_811_ = !lean_is_exclusive(v_i_786_);
if (v_isSharedCheck_811_ == 0)
{
v___x_804_ = v_i_786_;
v_isShared_805_ = v_isSharedCheck_811_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_ssize_802_);
lean_inc(v_usize_801_);
lean_inc(v_size_800_);
lean_inc(v_cidx_799_);
lean_inc(v_name_798_);
lean_dec(v_i_786_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_811_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_name_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_cidx_799_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_size_800_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_usize_801_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_ssize_802_);
v___x_807_ = v_reuseFailAlloc_810_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_808_, 0, v_var_789_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
lean_ctor_set(v___x_808_, 2, v_a_797_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*3, v_updateHeader_787_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
v___x_809_ = lean_apply_5(v_continueLet_788_, v___x_808_, v___y_790_, v___y_791_, v___y_792_, lean_box(0));
return v___x_809_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_var_789_);
lean_dec_ref(v_continueLet_788_);
lean_dec_ref(v_i_786_);
v_a_812_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_796_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_796_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_820_, lean_object* v_i_821_, lean_object* v_updateHeader_822_, lean_object* v_continueLet_823_, lean_object* v_var_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_updateHeader_9654__boxed_829_; lean_object* v_res_830_; 
v_updateHeader_9654__boxed_829_ = lean_unbox(v_updateHeader_822_);
v_res_830_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_820_, v_i_821_, v_updateHeader_9654__boxed_829_, v_continueLet_823_, v_var_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_831_, lean_object* v_var_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_837_, 0, v_var_832_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
v___x_838_ = lean_apply_5(v_continueLet_831_, v___x_837_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_839_, lean_object* v_var_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_839_, v_var_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_846_, lean_object* v_continueLet_847_, lean_object* v_id_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
size_t v_sz_853_; size_t v___x_854_; lean_object* v___x_855_; 
v_sz_853_ = lean_array_size(v_args_846_);
v___x_854_ = ((size_t)0ULL);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_853_, v___x_854_, v_args_846_, v___y_849_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
v___x_857_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_857_, 0, v_id_848_);
lean_ctor_set(v___x_857_, 1, v_a_856_);
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_849_);
v___x_858_ = lean_apply_5(v_continueLet_847_, v___x_857_, v___y_849_, v___y_850_, v___y_851_, lean_box(0));
return v___x_858_;
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_id_848_);
lean_dec_ref(v_continueLet_847_);
v_a_859_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_855_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_855_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_867_, lean_object* v_continueLet_868_, lean_object* v_id_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_867_, v_continueLet_868_, v_id_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_875_, lean_object* v_k_876_, lean_object* v_type_877_, lean_object* v_e_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_875_, v___y_879_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = l_Lean_IR_ToIR_lowerCode(v_k_876_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_890_, 0, v_a_884_);
lean_ctor_set(v___x_890_, 1, v_type_877_);
lean_ctor_set(v___x_890_, 2, v_e_878_);
lean_ctor_set(v___x_890_, 3, v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_dec(v_a_884_);
lean_dec_ref(v_e_878_);
lean_dec(v_type_877_);
return v___x_885_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_e_878_);
lean_dec(v_type_877_);
lean_dec_ref(v_k_876_);
v_a_895_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_883_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_883_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_903_, lean_object* v_k_904_, lean_object* v_type_905_, lean_object* v_e_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_903_, v_k_904_, v_type_905_, v_e_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_912_, lean_object* v_k_913_, lean_object* v_fvarId_914_, lean_object* v_f_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_914_, v_a_916_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
if (lean_obj_tag(v_a_921_) == 0)
{
lean_object* v_id_922_; lean_object* v___x_923_; 
lean_dec_ref(v_k_913_);
lean_dec_ref(v_decl_912_);
v_id_922_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_id_922_);
lean_dec_ref(v_a_921_);
lean_inc(v_a_918_);
lean_inc_ref(v_a_917_);
lean_inc(v_a_916_);
v___x_923_ = lean_apply_5(v_f_915_, v_id_922_, v_a_916_, v_a_917_, v_a_918_, lean_box(0));
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
lean_dec_ref(v_f_915_);
v___x_924_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_912_, v_k_913_, v_a_916_, v_a_917_, v_a_918_);
return v___x_924_;
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_f_915_);
lean_dec_ref(v_k_913_);
lean_dec_ref(v_decl_912_);
v_a_925_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_933_, lean_object* v_k_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_fvarId_939_; lean_object* v_type_940_; lean_object* v_value_941_; lean_object* v_type_942_; lean_object* v_continueLet_943_; 
v_fvarId_939_ = lean_ctor_get(v_decl_933_, 0);
v_type_940_ = lean_ctor_get(v_decl_933_, 2);
v_value_941_ = lean_ctor_get(v_decl_933_, 3);
lean_inc(v_value_941_);
v_type_942_ = l_Lean_IR_toIRType(v_type_940_);
lean_inc(v_type_942_);
lean_inc_ref(v_k_934_);
lean_inc(v_fvarId_939_);
v_continueLet_943_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_943_, 0, v_fvarId_939_);
lean_closure_set(v_continueLet_943_, 1, v_k_934_);
lean_closure_set(v_continueLet_943_, 2, v_type_942_);
switch(lean_obj_tag(v_value_941_))
{
case 0:
{
lean_object* v_value_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_954_; 
lean_inc(v_fvarId_939_);
lean_dec_ref(v_continueLet_943_);
lean_dec_ref(v_decl_933_);
v_value_944_ = lean_ctor_get(v_value_941_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_value_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_946_ = v_value_941_;
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_value_944_);
lean_dec(v_value_941_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v_fst_949_; lean_object* v___x_951_; 
v___x_948_ = l_Lean_IR_ToIR_lowerLitValue(v_value_944_);
v_fst_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_fst_949_);
lean_dec_ref(v___x_948_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 11);
lean_ctor_set(v___x_946_, 0, v_fst_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_fst_949_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_939_, v_k_934_, v_type_942_, v___x_951_, v_a_935_, v_a_936_, v_a_937_);
return v___x_952_;
}
}
}
case 1:
{
lean_object* v___x_955_; 
lean_dec_ref(v_continueLet_943_);
lean_dec(v_type_942_);
v___x_955_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_933_, v_k_934_, v_a_935_, v_a_936_, v_a_937_);
return v___x_955_;
}
case 4:
{
lean_object* v_fvarId_956_; lean_object* v_args_957_; lean_object* v___f_958_; lean_object* v___x_959_; 
lean_dec(v_type_942_);
v_fvarId_956_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_fvarId_956_);
v_args_957_ = lean_ctor_get(v_value_941_, 1);
lean_inc_ref(v_args_957_);
lean_dec_ref(v_value_941_);
v___f_958_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_958_, 0, v_args_957_);
lean_closure_set(v___f_958_, 1, v_continueLet_943_);
v___x_959_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_fvarId_956_, v___f_958_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_fvarId_956_);
return v___x_959_;
}
case 5:
{
lean_object* v_i_960_; lean_object* v_args_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_993_; 
lean_inc(v_fvarId_939_);
lean_dec_ref(v_continueLet_943_);
lean_dec_ref(v_decl_933_);
v_i_960_ = lean_ctor_get(v_value_941_, 0);
v_args_961_ = lean_ctor_get(v_value_941_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_value_941_);
if (v_isSharedCheck_993_ == 0)
{
v___x_963_ = v_value_941_;
v_isShared_964_ = v_isSharedCheck_993_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_args_961_);
lean_inc(v_i_960_);
lean_dec(v_value_941_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_993_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
size_t v_sz_965_; size_t v___x_966_; lean_object* v___x_967_; 
v_sz_965_ = lean_array_size(v_args_961_);
v___x_966_ = ((size_t)0ULL);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_965_, v___x_966_, v_args_961_, v_a_935_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v_name_969_; lean_object* v_cidx_970_; lean_object* v_size_971_; lean_object* v_usize_972_; lean_object* v_ssize_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_984_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref(v___x_967_);
v_name_969_ = lean_ctor_get(v_i_960_, 0);
v_cidx_970_ = lean_ctor_get(v_i_960_, 1);
v_size_971_ = lean_ctor_get(v_i_960_, 2);
v_usize_972_ = lean_ctor_get(v_i_960_, 3);
v_ssize_973_ = lean_ctor_get(v_i_960_, 4);
v_isSharedCheck_984_ = !lean_is_exclusive(v_i_960_);
if (v_isSharedCheck_984_ == 0)
{
v___x_975_ = v_i_960_;
v_isShared_976_ = v_isSharedCheck_984_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_ssize_973_);
lean_inc(v_usize_972_);
lean_inc(v_size_971_);
lean_inc(v_cidx_970_);
lean_inc(v_name_969_);
lean_dec(v_i_960_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_984_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_name_969_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_cidx_970_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_size_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_usize_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v_ssize_973_);
v___x_978_ = v_reuseFailAlloc_983_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 0);
lean_ctor_set(v___x_963_, 1, v_a_968_);
lean_ctor_set(v___x_963_, 0, v___x_978_);
v___x_980_ = v___x_963_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_a_968_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_939_, v_k_934_, v_type_942_, v___x_980_, v_a_935_, v_a_936_, v_a_937_);
return v___x_981_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_del_object(v___x_963_);
lean_dec_ref(v_i_960_);
lean_dec(v_type_942_);
lean_dec(v_fvarId_939_);
lean_dec_ref(v_k_934_);
v_a_985_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_967_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_967_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
case 6:
{
lean_object* v_i_994_; lean_object* v_var_995_; lean_object* v___f_996_; lean_object* v___x_997_; 
lean_dec(v_type_942_);
v_i_994_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_i_994_);
v_var_995_ = lean_ctor_get(v_value_941_, 1);
lean_inc(v_var_995_);
lean_dec_ref(v_value_941_);
v___f_996_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_996_, 0, v_i_994_);
lean_closure_set(v___f_996_, 1, v_continueLet_943_);
v___x_997_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_var_995_, v___f_996_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_var_995_);
return v___x_997_;
}
case 7:
{
lean_object* v_i_998_; lean_object* v_var_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; 
lean_dec(v_type_942_);
v_i_998_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_i_998_);
v_var_999_ = lean_ctor_get(v_value_941_, 1);
lean_inc(v_var_999_);
lean_dec_ref(v_value_941_);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1000_, 0, v_i_998_);
lean_closure_set(v___f_1000_, 1, v_continueLet_943_);
v___x_1001_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_var_999_, v___f_1000_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_var_999_);
return v___x_1001_;
}
case 8:
{
lean_object* v_n_1002_; lean_object* v_offset_1003_; lean_object* v_var_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; 
lean_dec(v_type_942_);
v_n_1002_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_n_1002_);
v_offset_1003_ = lean_ctor_get(v_value_941_, 1);
lean_inc(v_offset_1003_);
v_var_1004_ = lean_ctor_get(v_value_941_, 2);
lean_inc(v_var_1004_);
lean_dec_ref(v_value_941_);
v___f_1005_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1005_, 0, v_n_1002_);
lean_closure_set(v___f_1005_, 1, v_offset_1003_);
lean_closure_set(v___f_1005_, 2, v_continueLet_943_);
v___x_1006_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_var_1004_, v___f_1005_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_var_1004_);
return v___x_1006_;
}
case 9:
{
lean_object* v_fn_1007_; lean_object* v_args_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1028_; 
lean_inc(v_fvarId_939_);
lean_dec_ref(v_continueLet_943_);
lean_dec_ref(v_decl_933_);
v_fn_1007_ = lean_ctor_get(v_value_941_, 0);
v_args_1008_ = lean_ctor_get(v_value_941_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_value_941_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1010_ = v_value_941_;
v_isShared_1011_ = v_isSharedCheck_1028_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_args_1008_);
lean_inc(v_fn_1007_);
lean_dec(v_value_941_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1028_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
size_t v_sz_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v_sz_1012_ = lean_array_size(v_args_1008_);
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1012_, v___x_1013_, v_args_1008_, v_a_935_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 6);
lean_ctor_set(v___x_1010_, 1, v_a_1015_);
v___x_1017_ = v___x_1010_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_fn_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_a_1015_);
v___x_1017_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_939_, v_k_934_, v_type_942_, v___x_1017_, v_a_935_, v_a_936_, v_a_937_);
return v___x_1018_;
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_1010_);
lean_dec(v_fn_1007_);
lean_dec(v_type_942_);
lean_dec(v_fvarId_939_);
lean_dec_ref(v_k_934_);
v_a_1020_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1014_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1014_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1029_; lean_object* v_args_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1050_; 
lean_inc(v_fvarId_939_);
lean_dec_ref(v_continueLet_943_);
lean_dec_ref(v_decl_933_);
v_fn_1029_ = lean_ctor_get(v_value_941_, 0);
v_args_1030_ = lean_ctor_get(v_value_941_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_value_941_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1032_ = v_value_941_;
v_isShared_1033_ = v_isSharedCheck_1050_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_args_1030_);
lean_inc(v_fn_1029_);
lean_dec(v_value_941_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1050_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v_sz_1034_ = lean_array_size(v_args_1030_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1034_, v___x_1035_, v_args_1030_, v_a_935_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 7);
lean_ctor_set(v___x_1032_, 1, v_a_1037_);
v___x_1039_ = v___x_1032_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_fn_1029_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_a_1037_);
v___x_1039_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_939_, v_k_934_, v_type_942_, v___x_1039_, v_a_935_, v_a_936_, v_a_937_);
return v___x_1040_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_del_object(v___x_1032_);
lean_dec(v_fn_1029_);
lean_dec(v_type_942_);
lean_dec(v_fvarId_939_);
lean_dec_ref(v_k_934_);
v_a_1042_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1036_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1036_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1051_; lean_object* v_var_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
lean_dec(v_type_942_);
v_n_1051_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_n_1051_);
v_var_1052_ = lean_ctor_get(v_value_941_, 1);
lean_inc(v_var_1052_);
lean_dec_ref(v_value_941_);
v___f_1053_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1053_, 0, v_n_1051_);
lean_closure_set(v___f_1053_, 1, v_continueLet_943_);
v___x_1054_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_var_1052_, v___f_1053_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_var_1052_);
return v___x_1054_;
}
case 12:
{
lean_object* v_var_1055_; lean_object* v_i_1056_; uint8_t v_updateHeader_1057_; lean_object* v_args_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; 
lean_dec(v_type_942_);
v_var_1055_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_var_1055_);
v_i_1056_ = lean_ctor_get(v_value_941_, 1);
lean_inc_ref(v_i_1056_);
v_updateHeader_1057_ = lean_ctor_get_uint8(v_value_941_, sizeof(void*)*3);
v_args_1058_ = lean_ctor_get(v_value_941_, 2);
lean_inc_ref(v_args_1058_);
lean_dec_ref(v_value_941_);
v___x_1059_ = lean_box(v_updateHeader_1057_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1060_, 0, v_args_1058_);
lean_closure_set(v___f_1060_, 1, v_i_1056_);
lean_closure_set(v___f_1060_, 2, v___x_1059_);
lean_closure_set(v___f_1060_, 3, v_continueLet_943_);
v___x_1061_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_var_1055_, v___f_1060_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_var_1055_);
return v___x_1061_;
}
case 13:
{
lean_object* v_ty_1062_; lean_object* v_fvarId_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; 
lean_dec(v_type_942_);
v_ty_1062_ = lean_ctor_get(v_value_941_, 0);
lean_inc_ref(v_ty_1062_);
v_fvarId_1063_ = lean_ctor_get(v_value_941_, 1);
lean_inc(v_fvarId_1063_);
lean_dec_ref(v_value_941_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1064_, 0, v_ty_1062_);
lean_closure_set(v___f_1064_, 1, v_continueLet_943_);
v___x_1065_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_fvarId_1063_, v___f_1064_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_fvarId_1063_);
return v___x_1065_;
}
case 14:
{
lean_object* v_fvarId_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; 
lean_dec(v_type_942_);
v_fvarId_1066_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_fvarId_1066_);
lean_dec_ref(v_value_941_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1067_, 0, v_continueLet_943_);
v___x_1068_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_fvarId_1066_, v___f_1067_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_fvarId_1066_);
return v___x_1068_;
}
default: 
{
lean_object* v_fvarId_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
lean_dec(v_type_942_);
v_fvarId_1069_ = lean_ctor_get(v_value_941_, 0);
lean_inc(v_fvarId_1069_);
lean_dec_ref(v_value_941_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1070_, 0, v_continueLet_943_);
v___x_1071_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_933_, v_k_934_, v_fvarId_1069_, v___f_1070_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_fvarId_1069_);
return v___x_1071_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1075_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1076_ = lean_unsigned_to_nat(15u);
v___x_1077_ = lean_unsigned_to_nat(128u);
v___x_1078_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1079_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1080_ = l_mkPanicMessageWithDecl(v___x_1079_, v___x_1078_, v___x_1077_, v___x_1076_, v___x_1075_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
if (lean_obj_tag(v_a_1081_) == 1)
{
lean_object* v_info_1086_; lean_object* v_code_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1123_; 
v_info_1086_ = lean_ctor_get(v_a_1081_, 0);
v_code_1087_ = lean_ctor_get(v_a_1081_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_a_1081_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1089_ = v_a_1081_;
v_isShared_1090_ = v_isSharedCheck_1123_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_code_1087_);
lean_inc(v_info_1086_);
lean_dec(v_a_1081_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1123_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_IR_ToIR_lowerCode(v_code_1087_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1114_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1114_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1114_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_name_1096_; lean_object* v_cidx_1097_; lean_object* v_size_1098_; lean_object* v_usize_1099_; lean_object* v_ssize_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1113_; 
v_name_1096_ = lean_ctor_get(v_info_1086_, 0);
v_cidx_1097_ = lean_ctor_get(v_info_1086_, 1);
v_size_1098_ = lean_ctor_get(v_info_1086_, 2);
v_usize_1099_ = lean_ctor_get(v_info_1086_, 3);
v_ssize_1100_ = lean_ctor_get(v_info_1086_, 4);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_info_1086_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1102_ = v_info_1086_;
v_isShared_1103_ = v_isSharedCheck_1113_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_ssize_1100_);
lean_inc(v_usize_1099_);
lean_inc(v_size_1098_);
lean_inc(v_cidx_1097_);
lean_inc(v_name_1096_);
lean_dec(v_info_1086_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1113_;
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
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_name_1096_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_cidx_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_size_1098_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_usize_1099_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_ssize_1100_);
v___x_1105_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 0);
lean_ctor_set(v___x_1089_, 1, v_a_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1105_);
v___x_1107_ = v___x_1089_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_a_1092_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1107_);
v___x_1109_ = v___x_1094_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_del_object(v___x_1089_);
lean_dec_ref(v_info_1086_);
v_a_1115_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1091_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1091_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
lean_object* v_code_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1148_; 
v_code_1124_ = lean_ctor_get(v_a_1081_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_a_1081_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1126_ = v_a_1081_;
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_code_1124_);
lean_dec(v_a_1081_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_IR_ToIR_lowerCode(v_code_1124_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1139_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1139_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1139_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 1);
lean_ctor_set(v___x_1126_, 0, v_a_1129_);
v___x_1134_ = v___x_1126_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1126_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1149_, size_t v_i_1150_, lean_object* v_bs_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_lt(v_i_1150_, v_sz_1149_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_bs_1151_);
return v___x_1157_;
}
else
{
lean_object* v_v_1158_; lean_object* v___x_1159_; 
v_v_1158_ = lean_array_uget_borrowed(v_bs_1151_, v_i_1150_);
lean_inc(v_v_1158_);
v___x_1159_ = l_Lean_IR_ToIR_lowerAlt(v_v_1158_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v_bs_x27_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v_bs_x27_1162_ = lean_array_uset(v_bs_1151_, v_i_1150_, v___x_1161_);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_add(v_i_1150_, v___x_1163_);
v___x_1165_ = lean_array_uset(v_bs_x27_1162_, v_i_1150_, v_a_1160_);
v_i_1150_ = v___x_1164_;
v_bs_1151_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_bs_1151_);
v_a_1167_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1159_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1177_ = lean_unsigned_to_nat(53u);
v___x_1178_ = lean_unsigned_to_nat(95u);
v___x_1179_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1180_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1181_ = l_mkPanicMessageWithDecl(v___x_1180_, v___x_1179_, v___x_1178_, v___x_1177_, v___x_1176_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1182_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1183_ = lean_unsigned_to_nat(44u);
v___x_1184_ = lean_unsigned_to_nat(106u);
v___x_1185_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1186_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1187_ = l_mkPanicMessageWithDecl(v___x_1186_, v___x_1185_, v___x_1184_, v___x_1183_, v___x_1182_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1189_ = lean_unsigned_to_nat(44u);
v___x_1190_ = lean_unsigned_to_nat(114u);
v___x_1191_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1192_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1193_ = l_mkPanicMessageWithDecl(v___x_1192_, v___x_1191_, v___x_1190_, v___x_1189_, v___x_1188_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1195_ = lean_unsigned_to_nat(34u);
v___x_1196_ = lean_unsigned_to_nat(113u);
v___x_1197_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1198_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1199_ = l_mkPanicMessageWithDecl(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1201_ = lean_unsigned_to_nat(44u);
v___x_1202_ = lean_unsigned_to_nat(110u);
v___x_1203_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1204_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1205_ = l_mkPanicMessageWithDecl(v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1207_ = lean_unsigned_to_nat(34u);
v___x_1208_ = lean_unsigned_to_nat(109u);
v___x_1209_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1210_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1211_ = l_mkPanicMessageWithDecl(v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1213_ = lean_unsigned_to_nat(41u);
v___x_1214_ = lean_unsigned_to_nat(117u);
v___x_1215_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1216_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1217_ = l_mkPanicMessageWithDecl(v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1218_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1219_ = lean_unsigned_to_nat(41u);
v___x_1220_ = lean_unsigned_to_nat(120u);
v___x_1221_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1223_ = l_mkPanicMessageWithDecl(v___x_1222_, v___x_1221_, v___x_1220_, v___x_1219_, v___x_1218_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1225_ = lean_unsigned_to_nat(41u);
v___x_1226_ = lean_unsigned_to_nat(123u);
v___x_1227_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1228_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1229_ = l_mkPanicMessageWithDecl(v___x_1228_, v___x_1227_, v___x_1226_, v___x_1225_, v___x_1224_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1231_ = lean_unsigned_to_nat(41u);
v___x_1232_ = lean_unsigned_to_nat(126u);
v___x_1233_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1234_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1235_ = l_mkPanicMessageWithDecl(v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_, v___x_1230_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
switch(lean_obj_tag(v_c_1236_))
{
case 0:
{
lean_object* v_decl_1241_; lean_object* v_k_1242_; lean_object* v___x_1243_; 
v_decl_1241_ = lean_ctor_get(v_c_1236_, 0);
lean_inc_ref(v_decl_1241_);
v_k_1242_ = lean_ctor_get(v_c_1236_, 1);
lean_inc_ref(v_k_1242_);
lean_dec_ref(v_c_1236_);
v___x_1243_ = l_Lean_IR_ToIR_lowerLet(v_decl_1241_, v_k_1242_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1243_;
}
case 1:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_c_1236_);
v___x_1244_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1245_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1244_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1245_;
}
case 2:
{
lean_object* v_decl_1246_; lean_object* v_k_1247_; lean_object* v_fvarId_1248_; lean_object* v_params_1249_; lean_object* v_value_1250_; lean_object* v___x_1251_; 
v_decl_1246_ = lean_ctor_get(v_c_1236_, 0);
lean_inc_ref(v_decl_1246_);
v_k_1247_ = lean_ctor_get(v_c_1236_, 1);
lean_inc_ref(v_k_1247_);
lean_dec_ref(v_c_1236_);
v_fvarId_1248_ = lean_ctor_get(v_decl_1246_, 0);
lean_inc(v_fvarId_1248_);
v_params_1249_ = lean_ctor_get(v_decl_1246_, 2);
lean_inc_ref(v_params_1249_);
v_value_1250_ = lean_ctor_get(v_decl_1246_, 4);
lean_inc_ref(v_value_1250_);
lean_dec_ref(v_decl_1246_);
v___x_1251_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1248_, v_a_1237_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; size_t v_sz_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v_sz_1253_ = lean_array_size(v_params_1249_);
v___x_1254_ = ((size_t)0ULL);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1253_, v___x_1254_, v_params_1249_, v_a_1237_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = l_Lean_IR_ToIR_lowerCode(v_value_1250_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = l_Lean_IR_ToIR_lowerCode(v_k_1247_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1264_, 0, v_a_1252_);
lean_ctor_set(v___x_1264_, 1, v_a_1256_);
lean_ctor_set(v___x_1264_, 2, v_a_1258_);
lean_ctor_set(v___x_1264_, 3, v_a_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
lean_dec(v_a_1258_);
lean_dec(v_a_1256_);
lean_dec(v_a_1252_);
return v___x_1259_;
}
}
else
{
lean_dec(v_a_1256_);
lean_dec(v_a_1252_);
lean_dec_ref(v_k_1247_);
return v___x_1257_;
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_a_1252_);
lean_dec_ref(v_value_1250_);
lean_dec_ref(v_k_1247_);
v_a_1269_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1255_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1255_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_value_1250_);
lean_dec_ref(v_params_1249_);
lean_dec_ref(v_k_1247_);
v_a_1277_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1251_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1251_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1285_; lean_object* v_args_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1322_; 
v_fvarId_1285_ = lean_ctor_get(v_c_1236_, 0);
v_args_1286_ = lean_ctor_get(v_c_1236_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1288_ = v_c_1236_;
v_isShared_1289_ = v_isSharedCheck_1322_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_args_1286_);
lean_inc(v_fvarId_1285_);
lean_dec(v_c_1236_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1322_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1285_, v_a_1237_);
lean_dec(v_fvarId_1285_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; size_t v_sz_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref(v___x_1290_);
v_sz_1292_ = lean_array_size(v_args_1286_);
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1292_, v___x_1293_, v_args_1286_, v_a_1237_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1305_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1305_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1305_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 11);
lean_ctor_set(v___x_1288_, 1, v_a_1295_);
lean_ctor_set(v___x_1288_, 0, v_a_1291_);
v___x_1300_ = v___x_1288_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1291_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1291_);
lean_del_object(v___x_1288_);
v_a_1306_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1294_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1294_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1288_);
lean_dec_ref(v_args_1286_);
v_a_1314_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1290_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1290_);
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
}
case 4:
{
lean_object* v_cases_1323_; lean_object* v_typeName_1324_; lean_object* v_discr_1325_; lean_object* v_alts_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1366_; 
v_cases_1323_ = lean_ctor_get(v_c_1236_, 0);
lean_inc_ref(v_cases_1323_);
lean_dec_ref(v_c_1236_);
v_typeName_1324_ = lean_ctor_get(v_cases_1323_, 0);
v_discr_1325_ = lean_ctor_get(v_cases_1323_, 2);
v_alts_1326_ = lean_ctor_get(v_cases_1323_, 3);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_cases_1323_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v_cases_1323_, 1);
lean_dec(v_unused_1367_);
v___x_1328_ = v_cases_1323_;
v_isShared_1329_ = v_isSharedCheck_1366_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_alts_1326_);
lean_inc(v_discr_1325_);
lean_inc(v_typeName_1324_);
lean_dec(v_cases_1323_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1366_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1325_, v_a_1237_);
lean_dec(v_discr_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref(v___x_1330_);
if (lean_obj_tag(v_a_1331_) == 0)
{
lean_object* v_id_1332_; size_t v_sz_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v_id_1332_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_id_1332_);
lean_dec_ref(v_a_1331_);
v_sz_1333_ = lean_array_size(v_alts_1326_);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1333_, v___x_1334_, v_alts_1326_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1347_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = l_Lean_IR_nameToIRType(v_typeName_1324_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 9);
lean_ctor_set(v___x_1328_, 3, v_a_1336_);
lean_ctor_set(v___x_1328_, 2, v___x_1340_);
lean_ctor_set(v___x_1328_, 1, v_id_1332_);
v___x_1342_ = v___x_1328_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_typeName_1324_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_id_1332_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_a_1336_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1342_);
v___x_1344_ = v___x_1338_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v_id_1332_);
lean_del_object(v___x_1328_);
lean_dec(v_typeName_1324_);
v_a_1348_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1335_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1335_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_a_1331_);
lean_del_object(v___x_1328_);
lean_dec_ref(v_alts_1326_);
lean_dec(v_typeName_1324_);
v___x_1356_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1357_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1356_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1357_;
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_del_object(v___x_1328_);
lean_dec_ref(v_alts_1326_);
lean_dec(v_typeName_1324_);
v_a_1358_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1330_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1330_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1392_; 
v_fvarId_1368_ = lean_ctor_get(v_c_1236_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1370_ = v_c_1236_;
v_isShared_1371_ = v_isSharedCheck_1392_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_fvarId_1368_);
lean_dec(v_c_1236_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1392_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1368_, v_a_1237_);
lean_dec(v_fvarId_1368_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1383_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 10);
lean_ctor_set(v___x_1370_, 0, v_a_1373_);
v___x_1378_ = v___x_1370_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_del_object(v___x_1370_);
v_a_1384_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1372_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1372_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_c_1236_, 0);
lean_dec(v_unused_1401_);
v___x_1394_ = v_c_1236_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_c_1236_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_box(12);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
case 7:
{
lean_object* v_fvarId_1402_; lean_object* v_i_1403_; lean_object* v_y_1404_; lean_object* v_k_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1444_; 
v_fvarId_1402_ = lean_ctor_get(v_c_1236_, 0);
v_i_1403_ = lean_ctor_get(v_c_1236_, 1);
v_y_1404_ = lean_ctor_get(v_c_1236_, 2);
v_k_1405_ = lean_ctor_get(v_c_1236_, 3);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1407_ = v_c_1236_;
v_isShared_1408_ = v_isSharedCheck_1444_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_k_1405_);
lean_inc(v_y_1404_);
lean_inc(v_i_1403_);
lean_inc(v_fvarId_1402_);
lean_dec(v_c_1236_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1444_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1404_, v_a_1237_);
lean_dec(v_y_1404_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1402_, v_a_1237_);
lean_dec(v_fvarId_1402_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
if (lean_obj_tag(v_a_1412_) == 0)
{
lean_object* v_id_1413_; lean_object* v___x_1414_; 
v_id_1413_ = lean_ctor_get(v_a_1412_, 0);
lean_inc(v_id_1413_);
lean_dec_ref(v_a_1412_);
v___x_1414_ = l_Lean_IR_ToIR_lowerCode(v_k_1405_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1425_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 2);
lean_ctor_set(v___x_1407_, 3, v_a_1415_);
lean_ctor_set(v___x_1407_, 2, v_a_1410_);
lean_ctor_set(v___x_1407_, 0, v_id_1413_);
v___x_1420_ = v___x_1407_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_id_1413_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_i_1403_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_a_1410_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1420_);
v___x_1422_ = v___x_1417_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_dec(v_id_1413_);
lean_dec(v_a_1410_);
lean_del_object(v___x_1407_);
lean_dec(v_i_1403_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v_a_1412_);
lean_dec(v_a_1410_);
lean_del_object(v___x_1407_);
lean_dec_ref(v_k_1405_);
lean_dec(v_i_1403_);
v___x_1426_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1427_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1426_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1427_;
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1410_);
lean_del_object(v___x_1407_);
lean_dec_ref(v_k_1405_);
lean_dec(v_i_1403_);
v_a_1428_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1411_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1411_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_del_object(v___x_1407_);
lean_dec_ref(v_k_1405_);
lean_dec(v_i_1403_);
lean_dec(v_fvarId_1402_);
v_a_1436_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1409_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1409_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1445_; lean_object* v_i_1446_; lean_object* v_y_1447_; lean_object* v_k_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1490_; 
v_fvarId_1445_ = lean_ctor_get(v_c_1236_, 0);
v_i_1446_ = lean_ctor_get(v_c_1236_, 1);
v_y_1447_ = lean_ctor_get(v_c_1236_, 2);
v_k_1448_ = lean_ctor_get(v_c_1236_, 3);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1450_ = v_c_1236_;
v_isShared_1451_ = v_isSharedCheck_1490_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_k_1448_);
lean_inc(v_y_1447_);
lean_inc(v_i_1446_);
lean_inc(v_fvarId_1445_);
lean_dec(v_c_1236_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1490_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1447_, v_a_1237_);
lean_dec(v_y_1447_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1452_);
if (lean_obj_tag(v_a_1453_) == 0)
{
lean_object* v_id_1454_; lean_object* v___x_1455_; 
v_id_1454_ = lean_ctor_get(v_a_1453_, 0);
lean_inc(v_id_1454_);
lean_dec_ref(v_a_1453_);
v___x_1455_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1445_, v_a_1237_);
lean_dec(v_fvarId_1445_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
if (lean_obj_tag(v_a_1456_) == 0)
{
lean_object* v_id_1457_; lean_object* v___x_1458_; 
v_id_1457_ = lean_ctor_get(v_a_1456_, 0);
lean_inc(v_id_1457_);
lean_dec_ref(v_a_1456_);
v___x_1458_ = l_Lean_IR_ToIR_lowerCode(v_k_1448_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1469_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1469_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1469_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 4);
lean_ctor_set(v___x_1450_, 3, v_a_1459_);
lean_ctor_set(v___x_1450_, 2, v_id_1454_);
lean_ctor_set(v___x_1450_, 0, v_id_1457_);
v___x_1464_ = v___x_1450_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_id_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_i_1446_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_id_1454_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1464_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_dec(v_id_1457_);
lean_dec(v_id_1454_);
lean_del_object(v___x_1450_);
lean_dec(v_i_1446_);
return v___x_1458_;
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v_a_1456_);
lean_dec(v_id_1454_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_k_1448_);
lean_dec(v_i_1446_);
v___x_1470_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1471_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1470_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1471_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_id_1454_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_k_1448_);
lean_dec(v_i_1446_);
v_a_1472_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1455_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1455_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_a_1453_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_k_1448_);
lean_dec(v_i_1446_);
lean_dec(v_fvarId_1445_);
v___x_1480_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1481_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1480_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1481_;
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_del_object(v___x_1450_);
lean_dec_ref(v_k_1448_);
lean_dec(v_i_1446_);
lean_dec(v_fvarId_1445_);
v_a_1482_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1452_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1452_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1491_; lean_object* v_i_1492_; lean_object* v_offset_1493_; lean_object* v_y_1494_; lean_object* v_ty_1495_; lean_object* v_k_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1539_; 
v_fvarId_1491_ = lean_ctor_get(v_c_1236_, 0);
v_i_1492_ = lean_ctor_get(v_c_1236_, 1);
v_offset_1493_ = lean_ctor_get(v_c_1236_, 2);
v_y_1494_ = lean_ctor_get(v_c_1236_, 3);
v_ty_1495_ = lean_ctor_get(v_c_1236_, 4);
v_k_1496_ = lean_ctor_get(v_c_1236_, 5);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1498_ = v_c_1236_;
v_isShared_1499_ = v_isSharedCheck_1539_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_k_1496_);
lean_inc(v_ty_1495_);
lean_inc(v_y_1494_);
lean_inc(v_offset_1493_);
lean_inc(v_i_1492_);
lean_inc(v_fvarId_1491_);
lean_dec(v_c_1236_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1539_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1494_, v_a_1237_);
lean_dec(v_y_1494_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref(v___x_1500_);
if (lean_obj_tag(v_a_1501_) == 0)
{
lean_object* v_id_1502_; lean_object* v___x_1503_; 
v_id_1502_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_id_1502_);
lean_dec_ref(v_a_1501_);
v___x_1503_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1491_, v_a_1237_);
lean_dec(v_fvarId_1491_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
if (lean_obj_tag(v_a_1504_) == 0)
{
lean_object* v_id_1505_; lean_object* v___x_1506_; 
v_id_1505_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_id_1505_);
lean_dec_ref(v_a_1504_);
v___x_1506_ = l_Lean_IR_ToIR_lowerCode(v_k_1496_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1518_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1518_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1518_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = l_Lean_IR_toIRType(v_ty_1495_);
lean_dec_ref(v_ty_1495_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 5);
lean_ctor_set(v___x_1498_, 5, v_a_1507_);
lean_ctor_set(v___x_1498_, 4, v___x_1511_);
lean_ctor_set(v___x_1498_, 3, v_id_1502_);
lean_ctor_set(v___x_1498_, 0, v_id_1505_);
v___x_1513_ = v___x_1498_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_id_1505_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_i_1492_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_offset_1493_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_id_1502_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1517_, 5, v_a_1507_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1515_ = v___x_1509_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_dec(v_id_1505_);
lean_dec(v_id_1502_);
lean_del_object(v___x_1498_);
lean_dec_ref(v_ty_1495_);
lean_dec(v_offset_1493_);
lean_dec(v_i_1492_);
return v___x_1506_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v_a_1504_);
lean_dec(v_id_1502_);
lean_del_object(v___x_1498_);
lean_dec_ref(v_k_1496_);
lean_dec_ref(v_ty_1495_);
lean_dec(v_offset_1493_);
lean_dec(v_i_1492_);
v___x_1519_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1520_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1519_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1520_;
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_id_1502_);
lean_del_object(v___x_1498_);
lean_dec_ref(v_k_1496_);
lean_dec_ref(v_ty_1495_);
lean_dec(v_offset_1493_);
lean_dec(v_i_1492_);
v_a_1521_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1503_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1503_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1501_);
lean_del_object(v___x_1498_);
lean_dec_ref(v_k_1496_);
lean_dec_ref(v_ty_1495_);
lean_dec(v_offset_1493_);
lean_dec(v_i_1492_);
lean_dec(v_fvarId_1491_);
v___x_1529_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1530_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1529_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1530_;
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1498_);
lean_dec_ref(v_k_1496_);
lean_dec_ref(v_ty_1495_);
lean_dec(v_offset_1493_);
lean_dec(v_i_1492_);
lean_dec(v_fvarId_1491_);
v_a_1531_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1500_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1500_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1540_; lean_object* v_cidx_1541_; lean_object* v_k_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1571_; 
v_fvarId_1540_ = lean_ctor_get(v_c_1236_, 0);
v_cidx_1541_ = lean_ctor_get(v_c_1236_, 1);
v_k_1542_ = lean_ctor_get(v_c_1236_, 2);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1544_ = v_c_1236_;
v_isShared_1545_ = v_isSharedCheck_1571_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_k_1542_);
lean_inc(v_cidx_1541_);
lean_inc(v_fvarId_1540_);
lean_dec(v_c_1236_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1571_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1540_, v_a_1237_);
lean_dec(v_fvarId_1540_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
if (lean_obj_tag(v_a_1547_) == 0)
{
lean_object* v_id_1548_; lean_object* v___x_1549_; 
v_id_1548_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_id_1548_);
lean_dec_ref(v_a_1547_);
v___x_1549_ = l_Lean_IR_ToIR_lowerCode(v_k_1542_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1560_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 3);
lean_ctor_set(v___x_1544_, 2, v_a_1550_);
lean_ctor_set(v___x_1544_, 0, v_id_1548_);
v___x_1555_ = v___x_1544_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_id_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_cidx_1541_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1555_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_dec(v_id_1548_);
lean_del_object(v___x_1544_);
lean_dec(v_cidx_1541_);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v_a_1547_);
lean_del_object(v___x_1544_);
lean_dec_ref(v_k_1542_);
lean_dec(v_cidx_1541_);
v___x_1561_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1562_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1561_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1562_;
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1544_);
lean_dec_ref(v_k_1542_);
lean_dec(v_cidx_1541_);
v_a_1563_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1546_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1546_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1572_; lean_object* v_n_1573_; uint8_t v_check_1574_; uint8_t v_persistent_1575_; lean_object* v_k_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1605_; 
v_fvarId_1572_ = lean_ctor_get(v_c_1236_, 0);
v_n_1573_ = lean_ctor_get(v_c_1236_, 1);
v_check_1574_ = lean_ctor_get_uint8(v_c_1236_, sizeof(void*)*3);
v_persistent_1575_ = lean_ctor_get_uint8(v_c_1236_, sizeof(void*)*3 + 1);
v_k_1576_ = lean_ctor_get(v_c_1236_, 2);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1578_ = v_c_1236_;
v_isShared_1579_ = v_isSharedCheck_1605_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_k_1576_);
lean_inc(v_n_1573_);
lean_inc(v_fvarId_1572_);
lean_dec(v_c_1236_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1605_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1572_, v_a_1237_);
lean_dec(v_fvarId_1572_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
if (lean_obj_tag(v_a_1581_) == 0)
{
lean_object* v_id_1582_; lean_object* v___x_1583_; 
v_id_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_id_1582_);
lean_dec_ref(v_a_1581_);
v___x_1583_ = l_Lean_IR_ToIR_lowerCode(v_k_1576_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1594_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 6);
lean_ctor_set(v___x_1578_, 2, v_a_1584_);
lean_ctor_set(v___x_1578_, 0, v_id_1582_);
v___x_1589_ = v___x_1578_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_id_1582_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_n_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_a_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*3, v_check_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*3 + 1, v_persistent_1575_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_dec(v_id_1582_);
lean_del_object(v___x_1578_);
lean_dec(v_n_1573_);
return v___x_1583_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_a_1581_);
lean_del_object(v___x_1578_);
lean_dec_ref(v_k_1576_);
lean_dec(v_n_1573_);
v___x_1595_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1596_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1595_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1596_;
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1578_);
lean_dec_ref(v_k_1576_);
lean_dec(v_n_1573_);
v_a_1597_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1580_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1580_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1606_; lean_object* v_n_1607_; uint8_t v_check_1608_; uint8_t v_persistent_1609_; lean_object* v_k_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1639_; 
v_fvarId_1606_ = lean_ctor_get(v_c_1236_, 0);
v_n_1607_ = lean_ctor_get(v_c_1236_, 1);
v_check_1608_ = lean_ctor_get_uint8(v_c_1236_, sizeof(void*)*3);
v_persistent_1609_ = lean_ctor_get_uint8(v_c_1236_, sizeof(void*)*3 + 1);
v_k_1610_ = lean_ctor_get(v_c_1236_, 2);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1612_ = v_c_1236_;
v_isShared_1613_ = v_isSharedCheck_1639_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_k_1610_);
lean_inc(v_n_1607_);
lean_inc(v_fvarId_1606_);
lean_dec(v_c_1236_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1639_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1606_, v_a_1237_);
lean_dec(v_fvarId_1606_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
if (lean_obj_tag(v_a_1615_) == 0)
{
lean_object* v_id_1616_; lean_object* v___x_1617_; 
v_id_1616_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_id_1616_);
lean_dec_ref(v_a_1615_);
v___x_1617_ = l_Lean_IR_ToIR_lowerCode(v_k_1610_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1628_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1628_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1628_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 7);
lean_ctor_set(v___x_1612_, 2, v_a_1618_);
lean_ctor_set(v___x_1612_, 0, v_id_1616_);
v___x_1623_ = v___x_1612_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_id_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_n_1607_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_a_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3, v_check_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3 + 1, v_persistent_1609_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1623_);
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_dec(v_id_1616_);
lean_del_object(v___x_1612_);
lean_dec(v_n_1607_);
return v___x_1617_;
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v_a_1615_);
lean_del_object(v___x_1612_);
lean_dec_ref(v_k_1610_);
lean_dec(v_n_1607_);
v___x_1629_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1630_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1629_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1630_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_del_object(v___x_1612_);
lean_dec_ref(v_k_1610_);
lean_dec(v_n_1607_);
v_a_1631_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1614_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1614_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
default: 
{
lean_object* v_fvarId_1640_; lean_object* v_k_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1670_; 
v_fvarId_1640_ = lean_ctor_get(v_c_1236_, 0);
v_k_1641_ = lean_ctor_get(v_c_1236_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_c_1236_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1643_ = v_c_1236_;
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_k_1641_);
lean_inc(v_fvarId_1640_);
lean_dec(v_c_1236_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1640_, v_a_1237_);
lean_dec(v_fvarId_1640_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
if (lean_obj_tag(v_a_1646_) == 0)
{
lean_object* v_id_1647_; lean_object* v___x_1648_; 
v_id_1647_ = lean_ctor_get(v_a_1646_, 0);
lean_inc(v_id_1647_);
lean_dec_ref(v_a_1646_);
v___x_1648_ = l_Lean_IR_ToIR_lowerCode(v_k_1641_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1659_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1659_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1659_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 8);
lean_ctor_set(v___x_1643_, 1, v_a_1649_);
lean_ctor_set(v___x_1643_, 0, v_id_1647_);
v___x_1654_ = v___x_1643_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_id_1647_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1654_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_dec(v_id_1647_);
lean_del_object(v___x_1643_);
return v___x_1648_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v_a_1646_);
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1641_);
v___x_1660_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1661_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1660_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1661_;
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1643_);
lean_dec_ref(v_k_1641_);
v_a_1662_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1645_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1645_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1671_, lean_object* v_k_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_fvarId_1677_; lean_object* v___x_1678_; 
v_fvarId_1677_ = lean_ctor_get(v_decl_1671_, 0);
lean_inc(v_fvarId_1677_);
lean_dec_ref(v_decl_1671_);
v___x_1678_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1677_, v_a_1673_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref(v___x_1678_);
v___x_1679_ = l_Lean_IR_ToIR_lowerCode(v_k_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1679_;
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_k_1672_);
v_a_1680_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1678_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1688_, lean_object* v_k_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1688_, v_k_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1695_, lean_object* v_k_1696_, lean_object* v_fvarId_1697_, lean_object* v_f_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1695_, v_k_1696_, v_fvarId_1697_, v_f_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec(v_fvarId_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1704_, lean_object* v_i_1705_, lean_object* v_bs_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
size_t v_sz_boxed_1711_; size_t v_i_boxed_1712_; lean_object* v_res_1713_; 
v_sz_boxed_1711_ = lean_unbox_usize(v_sz_1704_);
lean_dec(v_sz_1704_);
v_i_boxed_1712_ = lean_unbox_usize(v_i_1705_);
lean_dec(v_i_1705_);
v_res_1713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1711_, v_i_boxed_1712_, v_bs_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_IR_ToIR_lowerAlt(v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1720_, lean_object* v_k_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_IR_ToIR_lowerLet(v_decl_1720_, v_k_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_IR_ToIR_lowerCode(v_c_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1733_, lean_object* v_k_1734_, lean_object* v_x_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1733_, v_k_1734_, v_a_1736_, v_a_1737_, v_a_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1741_, lean_object* v_k_1742_, lean_object* v_x_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1741_, v_k_1742_, v_x_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_bs_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1749_, v_i_1750_, v_bs_1751_, v___y_1752_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1757_, lean_object* v_i_1758_, lean_object* v_bs_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
size_t v_sz_boxed_1764_; size_t v_i_boxed_1765_; lean_object* v_res_1766_; 
v_sz_boxed_1764_ = lean_unbox_usize(v_sz_1757_);
lean_dec(v_sz_1757_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1758_);
lean_dec(v_i_1758_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1764_, v_i_boxed_1765_, v_bs_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1767_, size_t v_i_1768_, lean_object* v_bs_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1767_, v_i_1768_, v_bs_1769_, v___y_1770_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1775_, lean_object* v_i_1776_, lean_object* v_bs_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
size_t v_sz_boxed_1782_; size_t v_i_boxed_1783_; lean_object* v_res_1784_; 
v_sz_boxed_1782_ = lean_unbox_usize(v_sz_1775_);
lean_dec(v_sz_1775_);
v_i_boxed_1783_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1782_, v_i_boxed_1783_, v_bs_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_toSignature_1790_; lean_object* v_value_1791_; lean_object* v_name_1792_; lean_object* v_type_1793_; lean_object* v_params_1794_; size_t v_sz_1795_; size_t v___x_1796_; lean_object* v___x_1797_; 
v_toSignature_1790_ = lean_ctor_get(v_d_1785_, 0);
lean_inc_ref(v_toSignature_1790_);
v_value_1791_ = lean_ctor_get(v_d_1785_, 1);
lean_inc_ref(v_value_1791_);
lean_dec_ref(v_d_1785_);
v_name_1792_ = lean_ctor_get(v_toSignature_1790_, 0);
lean_inc(v_name_1792_);
v_type_1793_ = lean_ctor_get(v_toSignature_1790_, 2);
lean_inc_ref(v_type_1793_);
v_params_1794_ = lean_ctor_get(v_toSignature_1790_, 3);
lean_inc_ref(v_params_1794_);
lean_dec_ref(v_toSignature_1790_);
v_sz_1795_ = lean_array_size(v_params_1794_);
v___x_1796_ = ((size_t)0ULL);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1795_, v___x_1796_, v_params_1794_, v_a_1786_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1854_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1854_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1854_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_IR_toIRType(v_type_1793_);
lean_dec_ref(v_type_1793_);
if (lean_obj_tag(v_value_1791_) == 0)
{
lean_object* v_code_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1829_; 
lean_del_object(v___x_1800_);
v_code_1803_ = lean_ctor_get(v_value_1791_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_value_1791_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1805_ = v_value_1791_;
v_isShared_1806_ = v_isSharedCheck_1829_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_code_1803_);
lean_dec(v_value_1791_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1829_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_IR_ToIR_lowerCode(v_code_1803_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1820_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1813_, 0, v_name_1792_);
lean_ctor_set(v___x_1813_, 1, v_a_1798_);
lean_ctor_set(v___x_1813_, 2, v___x_1802_);
lean_ctor_set(v___x_1813_, 3, v_a_1808_);
lean_ctor_set(v___x_1813_, 4, v___x_1812_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 1);
lean_ctor_set(v___x_1805_, 0, v___x_1813_);
v___x_1815_ = v___x_1805_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1815_);
v___x_1817_ = v___x_1810_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_del_object(v___x_1805_);
lean_dec(v___x_1802_);
lean_dec(v_a_1798_);
lean_dec(v_name_1792_);
v_a_1821_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1807_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1807_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1853_; 
v_externAttrData_1830_ = lean_ctor_get(v_value_1791_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_value_1791_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1832_ = v_value_1791_;
v_isShared_1833_ = v_isSharedCheck_1853_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_externAttrData_1830_);
lean_dec(v_value_1791_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1853_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_List_isEmpty___redArg(v_externAttrData_1830_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1835_, 0, v_name_1792_);
lean_ctor_set(v___x_1835_, 1, v_a_1798_);
lean_ctor_set(v___x_1835_, 2, v___x_1802_);
lean_ctor_set(v___x_1835_, 3, v_externAttrData_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1837_);
v___x_1839_ = v___x_1800_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
lean_del_object(v___x_1832_);
lean_dec(v_externAttrData_1830_);
lean_del_object(v___x_1800_);
v___x_1842_ = l_Lean_IR_mkDummyExternDecl(v_name_1792_, v_a_1798_, v___x_1802_);
v___x_1843_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1842_, v_a_1788_);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1843_, 0);
lean_dec(v_unused_1852_);
v___x_1845_ = v___x_1843_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_dec(v___x_1843_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_type_1793_);
lean_dec(v_name_1792_);
lean_dec_ref(v_value_1791_);
v_a_1855_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1797_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1797_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_IR_ToIR_lowerDecl(v_d_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1869_, size_t v_sz_1870_, size_t v_i_1871_, lean_object* v_b_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_usize_dec_lt(v_i_1871_, v_sz_1870_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_b_1872_);
return v___x_1877_;
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_a_1878_ = lean_array_uget_borrowed(v_as_1869_, v_i_1871_);
lean_inc(v_a_1878_);
v___x_1879_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1879_, 0, v_a_1878_);
v___x_1880_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1879_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_a_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
if (lean_obj_tag(v_a_1881_) == 1)
{
lean_object* v_val_1887_; lean_object* v___x_1888_; 
v_val_1887_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_val_1887_);
lean_dec_ref(v_a_1881_);
v___x_1888_ = lean_array_push(v_b_1872_, v_val_1887_);
v_a_1883_ = v___x_1888_;
goto v___jp_1882_;
}
else
{
lean_dec(v_a_1881_);
v_a_1883_ = v_b_1872_;
goto v___jp_1882_;
}
v___jp_1882_:
{
size_t v___x_1884_; size_t v___x_1885_; 
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1871_, v___x_1884_);
v_i_1871_ = v___x_1885_;
v_b_1872_ = v_a_1883_;
goto _start;
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v_b_1872_);
v_a_1889_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1880_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1880_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1897_, lean_object* v_sz_1898_, lean_object* v_i_1899_, lean_object* v_b_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
size_t v_sz_boxed_1904_; size_t v_i_boxed_1905_; lean_object* v_res_1906_; 
v_sz_boxed_1904_ = lean_unbox_usize(v_sz_1898_);
lean_dec(v_sz_1898_);
v_i_boxed_1905_ = lean_unbox_usize(v_i_1899_);
lean_dec(v_i_1899_);
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1897_, v_sz_boxed_1904_, v_i_boxed_1905_, v_b_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec_ref(v_as_1897_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_irDecls_1913_; size_t v_sz_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v_irDecls_1913_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1914_ = lean_array_size(v_decls_1909_);
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1909_, v_sz_1914_, v___x_1915_, v_irDecls_1913_, v_a_1910_, v_a_1911_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_IR_toIR(v_decls_1917_, v_a_1918_, v_a_1919_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec_ref(v_decls_1917_);
return v_res_1921_;
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
