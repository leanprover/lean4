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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__1, &l_Lean_IR_ToIR_M_run___redArg___closed__1_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__0, &l_Lean_IR_ToIR_M_run___redArg___closed__0_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__2, &l_Lean_IR_ToIR_M_run___redArg___closed__2_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__2);
v___x_11_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_ctor_set(v___x_11_, 2, v___x_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* v_x_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__3, &l_Lean_IR_ToIR_M_run___redArg___closed__3_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__3);
v___x_17_ = lean_st_mk_ref(v___x_16_);
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v___x_17_);
v___x_18_ = lean_apply_4(v_x_12_, v___x_17_, v_a_13_, v_a_14_, lean_box(0));
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_27_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_27_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_st_ref_get(v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_23_);
if (v_isShared_22_ == 0)
{
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_19_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_dec(v___x_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object* v_x_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_IR_ToIR_M_run___redArg(v_x_28_, v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* v_00_u03b1_33_, lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_IR_ToIR_M_run___redArg(v_x_34_, v_a_35_, v_a_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object* v_00_u03b1_39_, lean_object* v_x_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_IR_ToIR_M_run(v_00_u03b1_39_, v_x_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_m_45_, lean_object* v_query_46_, lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_zero_50_; uint8_t v_isZero_51_; 
v_zero_50_ = lean_unsigned_to_nat(0u);
v_isZero_51_ = lean_nat_dec_eq(v_x_48_, v_zero_50_);
if (v_isZero_51_ == 1)
{
lean_dec(v_x_49_);
lean_dec(v_x_48_);
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(2);
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_val_53_ = lean_ctor_get(v_x_47_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v_x_47_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_val_53_);
lean_dec(v_x_47_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_val_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
else
{
lean_object* v_keyArray_61_; lean_object* v_valueArray_62_; lean_object* v___x_63_; uint8_t v_isSome_64_; 
v_keyArray_61_ = lean_ctor_get(v_m_45_, 1);
v_valueArray_62_ = lean_ctor_get(v_m_45_, 2);
v___x_63_ = lean_array_fget_borrowed(v_keyArray_61_, v_x_49_);
v_isSome_64_ = lean_noption_is_some(v___x_63_);
if (v_isSome_64_ == 0)
{
lean_dec(v_x_48_);
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v_x_49_);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
lean_dec(v_x_49_);
v_val_66_ = lean_ctor_get(v_x_47_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_47_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v_x_47_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_dec(v_x_47_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_val_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
else
{
lean_object* v_one_74_; lean_object* v_n_75_; lean_object* v___y_77_; 
v_one_74_ = lean_unsigned_to_nat(1u);
v_n_75_ = lean_nat_sub(v_x_48_, v_one_74_);
lean_dec(v_x_48_);
if (v_isSome_64_ == 0)
{
goto v___jp_83_;
}
else
{
lean_object* v___x_85_; uint8_t v_isSome_86_; 
v___x_85_ = lean_array_fget_borrowed(v_valueArray_62_, v_x_49_);
v_isSome_86_ = lean_noption_is_some(v___x_85_);
if (v_isSome_86_ == 0)
{
goto v___jp_83_;
}
else
{
lean_object* v_val_87_; uint8_t v___x_88_; 
lean_inc(v___x_63_);
v_val_87_ = lean_noption_get(v___x_63_);
v___x_88_ = l_Lean_instBEqFVarId_beq(v_val_87_, v_query_46_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
lean_dec(v_val_87_);
v___x_89_ = lean_array_get_size(v_keyArray_61_);
v___x_90_ = lean_nat_add(v_x_49_, v_one_74_);
lean_dec(v_x_49_);
v___x_91_ = lean_nat_dec_lt(v___x_90_, v___x_89_);
if (v___x_91_ == 0)
{
lean_dec(v___x_90_);
v_x_48_ = v_n_75_;
v_x_49_ = v_zero_50_;
goto _start;
}
else
{
v_x_48_ = v_n_75_;
v_x_49_ = v___x_90_;
goto _start;
}
}
else
{
lean_object* v_val_94_; lean_object* v___x_95_; 
lean_dec(v_n_75_);
lean_dec(v_x_47_);
lean_inc(v___x_85_);
v_val_94_ = lean_noption_get(v___x_85_);
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v_x_49_);
lean_ctor_set(v___x_95_, 1, v_val_87_);
lean_ctor_set(v___x_95_, 2, v_val_94_);
return v___x_95_;
}
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_array_get_size(v_keyArray_61_);
v___x_79_ = lean_nat_add(v_x_49_, v_one_74_);
lean_dec(v_x_49_);
v___x_80_ = lean_nat_dec_lt(v___x_79_, v___x_78_);
if (v___x_80_ == 0)
{
lean_dec(v___x_79_);
v_x_47_ = v___y_77_;
v_x_48_ = v_n_75_;
v_x_49_ = v_zero_50_;
goto _start;
}
else
{
v_x_47_ = v___y_77_;
v_x_48_ = v_n_75_;
v_x_49_ = v___x_79_;
goto _start;
}
}
v___jp_83_:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v___x_84_; 
lean_inc(v_x_49_);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v_x_49_);
v___y_77_ = v___x_84_;
goto v___jp_76_;
}
else
{
v___y_77_ = v_x_47_;
goto v___jp_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_m_96_, lean_object* v_query_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_m_96_, v_query_97_, v_x_98_, v_x_99_, v_x_100_);
lean_dec(v_query_97_);
lean_dec_ref(v_m_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_m_102_, lean_object* v_query_103_){
_start:
{
lean_object* v_keyArray_104_; lean_object* v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v_fold_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_keyArray_104_ = lean_ctor_get(v_m_102_, 1);
v___x_105_ = lean_array_get_size(v_keyArray_104_);
v___x_106_ = l_Lean_instHashableFVarId_hash(v_query_103_);
v___x_107_ = 32ULL;
v___x_108_ = lean_uint64_shift_right(v___x_106_, v___x_107_);
v_fold_109_ = lean_uint64_xor(v___x_106_, v___x_108_);
v___x_110_ = 16ULL;
v___x_111_ = lean_uint64_shift_right(v_fold_109_, v___x_110_);
v___x_112_ = lean_uint64_xor(v_fold_109_, v___x_111_);
v___x_113_ = lean_uint64_to_usize(v___x_112_);
v___x_114_ = lean_usize_of_nat(v___x_105_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_sub(v___x_114_, v___x_115_);
v___x_117_ = lean_usize_land(v___x_113_, v___x_116_);
v___x_118_ = lean_usize_to_nat(v___x_117_);
v___x_119_ = lean_box(0);
v___x_120_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_m_102_, v_query_103_, v___x_119_, v___x_105_, v___x_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_121_, lean_object* v_query_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_m_121_, v_query_122_);
lean_dec(v_query_122_);
lean_dec_ref(v_m_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object* v_m_124_, lean_object* v_query_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_m_124_, v_query_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_index_127_; lean_object* v_key_128_; lean_object* v_value_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_index_127_ = lean_ctor_get(v___x_126_, 0);
v_key_128_ = lean_ctor_get(v___x_126_, 1);
v_value_129_ = lean_ctor_get(v___x_126_, 2);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_126_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_value_129_);
lean_inc(v_key_128_);
lean_inc(v_index_127_);
lean_dec(v___x_126_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_index_127_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_key_128_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_value_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v___x_137_; 
lean_dec(v___x_126_);
v___x_137_ = lean_box(1);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_138_, lean_object* v_query_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(v_m_138_, v_query_139_);
lean_dec(v_query_139_);
lean_dec_ref(v_m_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object* v_m_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(v_m_141_, v_a_142_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_value_144_; lean_object* v___x_145_; 
v_value_144_ = lean_ctor_get(v___x_143_, 2);
lean_inc(v_value_144_);
lean_dec_ref_known(v___x_143_, 3);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v_value_144_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = lean_box(0);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object* v_m_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_m_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_m_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__1(lean_object* v_msg_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = l_Lean_IR_instInhabitedArg_default;
v___x_152_ = lean_panic_fn_borrowed(v___x_151_, v_msg_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__2));
v___x_157_ = lean_unsigned_to_nat(12u);
v___x_158_ = lean_unsigned_to_nat(672u);
v___x_159_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__1));
v___x_160_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__0));
v___x_161_ = l_mkPanicMessageWithDecl(v___x_160_, v___x_159_, v___x_158_, v___x_157_, v___x_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_m_162_, v_a_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3);
v___x_166_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__1(v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_val_167_; 
v_val_167_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_164_, 1);
return v_val_167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* v_m_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_m_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec_ref(v_m_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* v_fvarId_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_vars_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_st_ref_get(v_a_172_);
v_vars_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_vars_175_);
lean_dec(v___x_174_);
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_vars_175_, v_fvarId_171_);
lean_dec_ref(v_vars_175_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* v_fvarId_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec(v_fvarId_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* v_fvarId_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_182_, v_a_183_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* v_fvarId_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_IR_ToIR_getFVarValue(v_fvarId_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec(v_fvarId_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* v_00_u03b2_194_, lean_object* v_m_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_m_195_, v_a_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_198_, lean_object* v_m_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_00_u03b2_198_, v_m_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_m_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_202_, lean_object* v_m_203_, lean_object* v_query_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(v_m_203_, v_query_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_206_, lean_object* v_m_207_, lean_object* v_query_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(v_00_u03b2_206_, v_m_207_, v_query_208_);
lean_dec(v_query_208_);
lean_dec_ref(v_m_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_210_, lean_object* v_m_211_, lean_object* v_query_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_m_211_, v_query_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_214_, lean_object* v_m_215_, lean_object* v_query_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_214_, v_m_215_, v_query_216_);
lean_dec(v_query_216_);
lean_dec_ref(v_m_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_218_, lean_object* v_m_219_, lean_object* v_query_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_m_219_, v_query_220_, v_x_221_, v_x_222_, v_x_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b2_226_, lean_object* v_m_227_, lean_object* v_query_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3_spec__4(v_00_u03b2_226_, v_m_227_, v_query_228_, v_x_229_, v_x_230_, v_x_231_, v_x_232_);
lean_dec(v_query_228_);
lean_dec_ref(v_m_227_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(lean_object* v_msg_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_panic_fn_borrowed(v___x_235_, v_msg_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(v_m_237_, v_a_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___closed__3);
v___x_241_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_val_242_; 
v_val_242_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_239_, 1);
return v_val_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(lean_object* v_m_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_m_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_m_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* v_fvarId_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_joinPoints_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = lean_st_ref_get(v_a_247_);
v_joinPoints_250_ = lean_ctor_get(v___x_249_, 1);
lean_inc_ref(v_joinPoints_250_);
lean_dec(v___x_249_);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_joinPoints_250_, v_fvarId_246_);
lean_dec_ref(v_joinPoints_250_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* v_fvarId_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec(v_fvarId_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* v_fvarId_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_257_, v_a_258_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* v_fvarId_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_IR_ToIR_getJoinPointValue(v_fvarId_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec(v_fvarId_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg(lean_object* v_b_269_, lean_object* v_acc_270_, lean_object* v_i_271_){
_start:
{
lean_object* v___y_273_; lean_object* v_keyArray_281_; lean_object* v_valueArray_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_keyArray_281_ = lean_ctor_get(v_b_269_, 1);
v_valueArray_282_ = lean_ctor_get(v_b_269_, 2);
v___x_283_ = lean_array_get_size(v_keyArray_281_);
v___x_284_ = lean_nat_dec_lt(v_i_271_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec(v_i_271_);
return v_acc_270_;
}
else
{
lean_object* v___x_285_; uint8_t v_isSome_286_; 
v___x_285_ = lean_array_fget_borrowed(v_keyArray_281_, v_i_271_);
v_isSome_286_ = lean_noption_is_some(v___x_285_);
if (v_isSome_286_ == 0)
{
goto v___jp_277_;
}
else
{
lean_object* v___x_287_; uint8_t v_isSome_288_; 
v___x_287_ = lean_array_fget_borrowed(v_valueArray_282_, v_i_271_);
v_isSome_288_ = lean_noption_is_some(v___x_287_);
if (v_isSome_288_ == 0)
{
goto v___jp_277_;
}
else
{
lean_object* v_val_289_; lean_object* v_val_290_; lean_object* v_i_292_; lean_object* v___x_297_; 
lean_inc(v___x_285_);
v_val_289_ = lean_noption_get(v___x_285_);
lean_inc(v___x_287_);
v_val_290_ = lean_noption_get(v___x_287_);
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_acc_270_, v_val_289_);
switch(lean_obj_tag(v___x_297_))
{
case 0:
{
lean_object* v_index_298_; lean_object* v_size_299_; lean_object* v___x_300_; 
v_index_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_index_298_);
lean_dec_ref_known(v___x_297_, 3);
v_size_299_ = lean_ctor_get(v_acc_270_, 0);
lean_inc(v_size_299_);
v___x_300_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_270_, v_size_299_, v_index_298_, v_val_289_, v_val_290_);
lean_dec(v_index_298_);
v___y_273_ = v___x_300_;
goto v___jp_272_;
}
case 1:
{
lean_object* v_index_301_; 
v_index_301_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_index_301_);
lean_dec_ref_known(v___x_297_, 1);
v_i_292_ = v_index_301_;
goto v___jp_291_;
}
default: 
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_270_, v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_index_304_; 
v_index_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_index_304_);
lean_dec_ref_known(v___x_303_, 1);
v_i_292_ = v_index_304_;
goto v___jp_291_;
}
else
{
lean_dec(v_val_290_);
lean_dec(v_val_289_);
v___y_273_ = v_acc_270_;
goto v___jp_272_;
}
}
}
v___jp_291_:
{
lean_object* v_size_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_size_293_ = lean_ctor_get(v_acc_270_, 0);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_size_293_, v___x_294_);
v___x_296_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_270_, v___x_295_, v_i_292_, v_val_289_, v_val_290_);
lean_dec(v_i_292_);
v___y_273_ = v___x_296_;
goto v___jp_272_;
}
}
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_add(v_i_271_, v___x_274_);
lean_dec(v_i_271_);
v_acc_270_ = v___y_273_;
v_i_271_ = v___x_275_;
goto _start;
}
v___jp_277_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_i_271_, v___x_278_);
lean_dec(v_i_271_);
v_i_271_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_b_305_, lean_object* v_acc_306_, lean_object* v_i_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg(v_b_305_, v_acc_306_, v_i_307_);
lean_dec_ref(v_b_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* v_init_309_, lean_object* v_b_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg(v_b_310_, v_init_309_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* v_init_313_, lean_object* v_b_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_init_313_, v_b_314_);
lean_dec_ref(v_b_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* v_m_316_){
_start:
{
lean_object* v_keyArray_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_cellCount_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_target_324_; lean_object* v___x_325_; 
v_keyArray_317_ = lean_ctor_get(v_m_316_, 1);
v___x_318_ = lean_array_get_size(v_keyArray_317_);
v___x_319_ = lean_unsigned_to_nat(2u);
v_cellCount_320_ = lean_nat_mul(v___x_318_, v___x_319_);
v___x_321_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_320_);
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_320_);
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_320_);
v_target_324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_324_, 0, v___x_321_);
lean_ctor_set(v_target_324_, 1, v___x_322_);
lean_ctor_set(v_target_324_, 2, v___x_323_);
v___x_325_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_target_324_, v_m_316_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg___boxed(lean_object* v_m_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_326_);
lean_dec_ref(v_m_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* v_fvarId_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; lean_object* v_vars_332_; lean_object* v_joinPoints_333_; lean_object* v_nextId_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_409_; 
v___x_331_ = lean_st_ref_take(v_a_329_);
v_vars_332_ = lean_ctor_get(v___x_331_, 0);
v_joinPoints_333_ = lean_ctor_get(v___x_331_, 1);
v_nextId_334_ = lean_ctor_get(v___x_331_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_409_ == 0)
{
v___x_336_ = v___x_331_;
v_isShared_337_ = v_isSharedCheck_409_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_nextId_334_);
lean_inc(v_joinPoints_333_);
lean_inc(v_vars_332_);
lean_dec(v___x_331_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_409_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___y_339_; lean_object* v___x_347_; lean_object* v___y_349_; lean_object* v_i_350_; lean_object* v___y_356_; lean_object* v___y_366_; lean_object* v_i_367_; lean_object* v___x_382_; 
lean_inc(v_nextId_334_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_nextId_334_);
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_vars_332_, v_fvarId_328_);
switch(lean_obj_tag(v___x_382_))
{
case 0:
{
lean_dec_ref_known(v___x_382_, 3);
lean_dec_ref_known(v___x_347_, 1);
lean_dec(v_fvarId_328_);
v___y_339_ = v_vars_332_;
goto v___jp_338_;
}
case 1:
{
lean_object* v_index_383_; lean_object* v_size_384_; lean_object* v_keyArray_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v_index_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_index_383_);
lean_dec_ref_known(v___x_382_, 1);
v_size_384_ = lean_ctor_get(v_vars_332_, 0);
v_keyArray_385_ = lean_ctor_get(v_vars_332_, 1);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_size_384_, v___x_386_);
v___x_388_ = lean_array_get_size(v_keyArray_385_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_dec(v___x_387_);
lean_dec(v_index_383_);
goto v___jp_372_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_390_ = lean_unsigned_to_nat(4u);
v___x_391_ = lean_nat_mul(v___x_387_, v___x_390_);
v___x_392_ = lean_unsigned_to_nat(3u);
v___x_393_ = lean_nat_mul(v___x_388_, v___x_392_);
v___x_394_ = lean_nat_dec_le(v___x_391_, v___x_393_);
lean_dec(v___x_393_);
lean_dec(v___x_391_);
if (v___x_394_ == 0)
{
lean_dec(v___x_387_);
lean_dec(v_index_383_);
goto v___jp_372_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DHashMap_Raw_setEntry___redArg(v_vars_332_, v___x_387_, v_index_383_, v_fvarId_328_, v___x_347_);
lean_dec(v_index_383_);
v___y_339_ = v___x_395_;
goto v___jp_338_;
}
}
}
default: 
{
lean_object* v_size_396_; lean_object* v_keyArray_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_size_396_ = lean_ctor_get(v_vars_332_, 0);
v_keyArray_397_ = lean_ctor_get(v_vars_332_, 1);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_size_396_, v___x_398_);
v___x_400_ = lean_array_get_size(v_keyArray_397_);
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v___x_399_);
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_332_);
lean_dec_ref(v_vars_332_);
v___y_356_ = v___x_402_;
goto v___jp_355_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_403_ = lean_unsigned_to_nat(4u);
v___x_404_ = lean_nat_mul(v___x_399_, v___x_403_);
lean_dec(v___x_399_);
v___x_405_ = lean_unsigned_to_nat(3u);
v___x_406_ = lean_nat_mul(v___x_400_, v___x_405_);
v___x_407_ = lean_nat_dec_le(v___x_404_, v___x_406_);
lean_dec(v___x_406_);
lean_dec(v___x_404_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_332_);
lean_dec_ref(v_vars_332_);
v___y_356_ = v___x_408_;
goto v___jp_355_;
}
else
{
v___y_356_ = v_vars_332_;
goto v___jp_355_;
}
}
}
}
v___jp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_nextId_334_, v___x_340_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 2, v___x_341_);
lean_ctor_set(v___x_336_, 0, v___y_339_);
v___x_343_ = v___x_336_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___y_339_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_joinPoints_333_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v___x_341_);
v___x_343_ = v_reuseFailAlloc_346_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_st_ref_put(v_a_329_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_nextId_334_);
return v___x_345_;
}
}
v___jp_348_:
{
lean_object* v_size_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_size_351_ = lean_ctor_get(v___y_349_, 0);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_size_351_, v___x_352_);
v___x_354_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_349_, v___x_353_, v_i_350_, v_fvarId_328_, v___x_347_);
lean_dec(v_i_350_);
v___y_339_ = v___x_354_;
goto v___jp_338_;
}
v___jp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v___y_356_, v_fvarId_328_);
switch(lean_obj_tag(v___x_357_))
{
case 0:
{
lean_object* v_index_358_; lean_object* v_size_359_; lean_object* v___x_360_; 
v_index_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_index_358_);
lean_dec_ref_known(v___x_357_, 3);
v_size_359_ = lean_ctor_get(v___y_356_, 0);
lean_inc(v_size_359_);
v___x_360_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_356_, v_size_359_, v_index_358_, v_fvarId_328_, v___x_347_);
lean_dec(v_index_358_);
v___y_339_ = v___x_360_;
goto v___jp_338_;
}
case 1:
{
lean_object* v_index_361_; 
v_index_361_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_index_361_);
lean_dec_ref_known(v___x_357_, 1);
v___y_349_ = v___y_356_;
v_i_350_ = v_index_361_;
goto v___jp_348_;
}
default: 
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_356_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_index_364_; 
v_index_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_index_364_);
lean_dec_ref_known(v___x_363_, 1);
v___y_349_ = v___y_356_;
v_i_350_ = v_index_364_;
goto v___jp_348_;
}
else
{
lean_dec_ref_known(v___x_347_, 1);
lean_dec(v_fvarId_328_);
v___y_339_ = v___y_356_;
goto v___jp_338_;
}
}
}
}
v___jp_365_:
{
lean_object* v_size_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_size_368_ = lean_ctor_get(v___y_366_, 0);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_size_368_, v___x_369_);
v___x_371_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_366_, v___x_370_, v_i_367_, v_fvarId_328_, v___x_347_);
lean_dec(v_i_367_);
v___y_339_ = v___x_371_;
goto v___jp_338_;
}
v___jp_372_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_332_);
lean_dec_ref(v_vars_332_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_373_, v_fvarId_328_);
switch(lean_obj_tag(v___x_374_))
{
case 0:
{
lean_object* v_index_375_; lean_object* v_size_376_; lean_object* v___x_377_; 
v_index_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_index_375_);
lean_dec_ref_known(v___x_374_, 3);
v_size_376_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_size_376_);
v___x_377_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_373_, v_size_376_, v_index_375_, v_fvarId_328_, v___x_347_);
lean_dec(v_index_375_);
v___y_339_ = v___x_377_;
goto v___jp_338_;
}
case 1:
{
lean_object* v_index_378_; 
v_index_378_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_index_378_);
lean_dec_ref_known(v___x_374_, 1);
v___y_366_ = v___x_373_;
v_i_367_ = v_index_378_;
goto v___jp_365_;
}
default: 
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_373_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_index_381_; 
v_index_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_index_381_);
lean_dec_ref_known(v___x_380_, 1);
v___y_366_ = v___x_373_;
v_i_367_ = v_index_381_;
goto v___jp_365_;
}
else
{
lean_dec_ref_known(v___x_347_, 1);
lean_dec(v_fvarId_328_);
v___y_339_ = v___x_373_;
goto v___jp_338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_410_, v_a_411_);
lean_dec(v_a_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_414_, v_a_415_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_IR_ToIR_bindVar(v_fvarId_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_426_, lean_object* v_m_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_m_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0(v_00_u03b2_429_, v_m_430_);
lean_dec_ref(v_m_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_432_, lean_object* v_init_433_, lean_object* v_b_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_init_433_, v_b_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_436_, lean_object* v_init_437_, lean_object* v_b_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_436_, v_init_437_, v_b_438_);
lean_dec_ref(v_b_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_440_, lean_object* v_b_441_, lean_object* v_acc_442_, lean_object* v_i_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___redArg(v_b_441_, v_acc_442_, v_i_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_445_, lean_object* v_b_446_, lean_object* v_acc_447_, lean_object* v_i_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0_spec__1(v_00_u03b2_445_, v_b_446_, v_acc_447_, v_i_448_);
lean_dec_ref(v_b_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; lean_object* v_vars_454_; lean_object* v_joinPoints_455_; lean_object* v_nextId_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_530_; 
v___x_453_ = lean_st_ref_take(v_a_451_);
v_vars_454_ = lean_ctor_get(v___x_453_, 0);
v_joinPoints_455_ = lean_ctor_get(v___x_453_, 1);
v_nextId_456_ = lean_ctor_get(v___x_453_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_530_ == 0)
{
v___x_458_ = v___x_453_;
v_isShared_459_ = v_isSharedCheck_530_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_nextId_456_);
lean_inc(v_joinPoints_455_);
lean_inc(v_vars_454_);
lean_dec(v___x_453_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_530_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___y_461_; lean_object* v___y_470_; lean_object* v_i_471_; lean_object* v___y_487_; lean_object* v_i_488_; lean_object* v___y_494_; lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_joinPoints_455_, v_fvarId_450_);
switch(lean_obj_tag(v___x_503_))
{
case 0:
{
lean_dec_ref_known(v___x_503_, 3);
lean_dec(v_fvarId_450_);
v___y_461_ = v_joinPoints_455_;
goto v___jp_460_;
}
case 1:
{
lean_object* v_index_504_; lean_object* v_size_505_; lean_object* v_keyArray_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_index_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_index_504_);
lean_dec_ref_known(v___x_503_, 1);
v_size_505_ = lean_ctor_get(v_joinPoints_455_, 0);
v_keyArray_506_ = lean_ctor_get(v_joinPoints_455_, 1);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_size_505_, v___x_507_);
v___x_509_ = lean_array_get_size(v_keyArray_506_);
v___x_510_ = lean_nat_dec_lt(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec(v___x_508_);
lean_dec(v_index_504_);
goto v___jp_476_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_511_ = lean_unsigned_to_nat(4u);
v___x_512_ = lean_nat_mul(v___x_508_, v___x_511_);
v___x_513_ = lean_unsigned_to_nat(3u);
v___x_514_ = lean_nat_mul(v___x_509_, v___x_513_);
v___x_515_ = lean_nat_dec_le(v___x_512_, v___x_514_);
lean_dec(v___x_514_);
lean_dec(v___x_512_);
if (v___x_515_ == 0)
{
lean_dec(v___x_508_);
lean_dec(v_index_504_);
goto v___jp_476_;
}
else
{
lean_object* v___x_516_; 
lean_inc(v_nextId_456_);
v___x_516_ = l_Std_DHashMap_Raw_setEntry___redArg(v_joinPoints_455_, v___x_508_, v_index_504_, v_fvarId_450_, v_nextId_456_);
lean_dec(v_index_504_);
v___y_461_ = v___x_516_;
goto v___jp_460_;
}
}
}
default: 
{
lean_object* v_size_517_; lean_object* v_keyArray_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_size_517_ = lean_ctor_get(v_joinPoints_455_, 0);
v_keyArray_518_ = lean_ctor_get(v_joinPoints_455_, 1);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_size_517_, v___x_519_);
v___x_521_ = lean_array_get_size(v_keyArray_518_);
v___x_522_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v___x_520_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_455_);
lean_dec_ref(v_joinPoints_455_);
v___y_494_ = v___x_523_;
goto v___jp_493_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_524_ = lean_unsigned_to_nat(4u);
v___x_525_ = lean_nat_mul(v___x_520_, v___x_524_);
lean_dec(v___x_520_);
v___x_526_ = lean_unsigned_to_nat(3u);
v___x_527_ = lean_nat_mul(v___x_521_, v___x_526_);
v___x_528_ = lean_nat_dec_le(v___x_525_, v___x_527_);
lean_dec(v___x_527_);
lean_dec(v___x_525_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_455_);
lean_dec_ref(v_joinPoints_455_);
v___y_494_ = v___x_529_;
goto v___jp_493_;
}
else
{
v___y_494_ = v_joinPoints_455_;
goto v___jp_493_;
}
}
}
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = lean_nat_add(v_nextId_456_, v___x_462_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 2, v___x_463_);
lean_ctor_set(v___x_458_, 1, v___y_461_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_vars_454_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___y_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v___x_463_);
v___x_465_ = v_reuseFailAlloc_468_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_st_ref_put(v_a_451_, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_nextId_456_);
return v___x_467_;
}
}
v___jp_469_:
{
lean_object* v_size_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_size_472_ = lean_ctor_get(v___y_470_, 0);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_size_472_, v___x_473_);
lean_inc(v_nextId_456_);
v___x_475_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_470_, v___x_474_, v_i_471_, v_fvarId_450_, v_nextId_456_);
lean_dec(v_i_471_);
v___y_461_ = v___x_475_;
goto v___jp_460_;
}
v___jp_476_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_455_);
lean_dec_ref(v_joinPoints_455_);
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_477_, v_fvarId_450_);
switch(lean_obj_tag(v___x_478_))
{
case 0:
{
lean_object* v_index_479_; lean_object* v_size_480_; lean_object* v___x_481_; 
v_index_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_index_479_);
lean_dec_ref_known(v___x_478_, 3);
v_size_480_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_size_480_);
lean_inc(v_nextId_456_);
v___x_481_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_477_, v_size_480_, v_index_479_, v_fvarId_450_, v_nextId_456_);
lean_dec(v_index_479_);
v___y_461_ = v___x_481_;
goto v___jp_460_;
}
case 1:
{
lean_object* v_index_482_; 
v_index_482_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_index_482_);
lean_dec_ref_known(v___x_478_, 1);
v___y_470_ = v___x_477_;
v_i_471_ = v_index_482_;
goto v___jp_469_;
}
default: 
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_477_, v___x_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_index_485_; 
v_index_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_index_485_);
lean_dec_ref_known(v___x_484_, 1);
v___y_470_ = v___x_477_;
v_i_471_ = v_index_485_;
goto v___jp_469_;
}
else
{
lean_dec(v_fvarId_450_);
v___y_461_ = v___x_477_;
goto v___jp_460_;
}
}
}
}
v___jp_486_:
{
lean_object* v_size_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_size_489_ = lean_ctor_get(v___y_487_, 0);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_size_489_, v___x_490_);
lean_inc(v_nextId_456_);
v___x_492_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_487_, v___x_491_, v_i_488_, v_fvarId_450_, v_nextId_456_);
lean_dec(v_i_488_);
v___y_461_ = v___x_492_;
goto v___jp_460_;
}
v___jp_493_:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v___y_494_, v_fvarId_450_);
switch(lean_obj_tag(v___x_495_))
{
case 0:
{
lean_object* v_index_496_; lean_object* v_size_497_; lean_object* v___x_498_; 
v_index_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_index_496_);
lean_dec_ref_known(v___x_495_, 3);
v_size_497_ = lean_ctor_get(v___y_494_, 0);
lean_inc(v_size_497_);
lean_inc(v_nextId_456_);
v___x_498_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_494_, v_size_497_, v_index_496_, v_fvarId_450_, v_nextId_456_);
lean_dec(v_index_496_);
v___y_461_ = v___x_498_;
goto v___jp_460_;
}
case 1:
{
lean_object* v_index_499_; 
v_index_499_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_index_499_);
lean_dec_ref_known(v___x_495_, 1);
v___y_487_ = v___y_494_;
v_i_488_ = v_index_499_;
goto v___jp_486_;
}
default: 
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_494_, v___x_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_index_502_; 
v_index_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_index_502_);
lean_dec_ref_known(v___x_501_, 1);
v___y_487_ = v___y_494_;
v_i_488_ = v_index_502_;
goto v___jp_486_;
}
else
{
lean_dec(v_fvarId_450_);
v___y_461_ = v___y_494_;
goto v___jp_460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_531_, v_a_532_);
lean_dec(v_a_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_535_, v_a_536_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; lean_object* v_vars_551_; lean_object* v_joinPoints_552_; lean_object* v_nextId_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_627_; 
v___x_550_ = lean_st_ref_take(v_a_548_);
v_vars_551_ = lean_ctor_get(v___x_550_, 0);
v_joinPoints_552_ = lean_ctor_get(v___x_550_, 1);
v_nextId_553_ = lean_ctor_get(v___x_550_, 2);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_627_ == 0)
{
v___x_555_ = v___x_550_;
v_isShared_556_ = v_isSharedCheck_627_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_nextId_553_);
lean_inc(v_joinPoints_552_);
lean_inc(v_vars_551_);
lean_dec(v___x_550_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_627_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___y_559_; lean_object* v___x_565_; lean_object* v___y_567_; lean_object* v_i_568_; lean_object* v___y_574_; lean_object* v___y_584_; lean_object* v_i_585_; lean_object* v___x_600_; 
v___x_557_ = lean_box(0);
v___x_565_ = lean_box(1);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v_vars_551_, v_fvarId_547_);
switch(lean_obj_tag(v___x_600_))
{
case 0:
{
lean_dec_ref_known(v___x_600_, 3);
lean_dec(v_fvarId_547_);
v___y_559_ = v_vars_551_;
goto v___jp_558_;
}
case 1:
{
lean_object* v_index_601_; lean_object* v_size_602_; lean_object* v_keyArray_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 1);
v_size_602_ = lean_ctor_get(v_vars_551_, 0);
v_keyArray_603_ = lean_ctor_get(v_vars_551_, 1);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_size_602_, v___x_604_);
v___x_606_ = lean_array_get_size(v_keyArray_603_);
v___x_607_ = lean_nat_dec_lt(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_dec(v___x_605_);
lean_dec(v_index_601_);
goto v___jp_590_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_608_ = lean_unsigned_to_nat(4u);
v___x_609_ = lean_nat_mul(v___x_605_, v___x_608_);
v___x_610_ = lean_unsigned_to_nat(3u);
v___x_611_ = lean_nat_mul(v___x_606_, v___x_610_);
v___x_612_ = lean_nat_dec_le(v___x_609_, v___x_611_);
lean_dec(v___x_611_);
lean_dec(v___x_609_);
if (v___x_612_ == 0)
{
lean_dec(v___x_605_);
lean_dec(v_index_601_);
goto v___jp_590_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Raw_setEntry___redArg(v_vars_551_, v___x_605_, v_index_601_, v_fvarId_547_, v___x_565_);
lean_dec(v_index_601_);
v___y_559_ = v___x_613_;
goto v___jp_558_;
}
}
}
default: 
{
lean_object* v_size_614_; lean_object* v_keyArray_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_size_614_ = lean_ctor_get(v_vars_551_, 0);
v_keyArray_615_ = lean_ctor_get(v_vars_551_, 1);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_size_614_, v___x_616_);
v___x_618_ = lean_array_get_size(v_keyArray_615_);
v___x_619_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v___x_617_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_551_);
lean_dec_ref(v_vars_551_);
v___y_574_ = v___x_620_;
goto v___jp_573_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_621_ = lean_unsigned_to_nat(4u);
v___x_622_ = lean_nat_mul(v___x_617_, v___x_621_);
lean_dec(v___x_617_);
v___x_623_ = lean_unsigned_to_nat(3u);
v___x_624_ = lean_nat_mul(v___x_618_, v___x_623_);
v___x_625_ = lean_nat_dec_le(v___x_622_, v___x_624_);
lean_dec(v___x_624_);
lean_dec(v___x_622_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_551_);
lean_dec_ref(v_vars_551_);
v___y_574_ = v___x_626_;
goto v___jp_573_;
}
else
{
v___y_574_ = v_vars_551_;
goto v___jp_573_;
}
}
}
}
v___jp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___y_559_);
v___x_561_ = v___x_555_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___y_559_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_joinPoints_552_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_nextId_553_);
v___x_561_ = v_reuseFailAlloc_564_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_st_ref_put(v_a_548_, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_557_);
return v___x_563_;
}
}
v___jp_566_:
{
lean_object* v_size_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_size_569_ = lean_ctor_get(v___y_567_, 0);
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_size_569_, v___x_570_);
v___x_572_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_567_, v___x_571_, v_i_568_, v_fvarId_547_, v___x_565_);
lean_dec(v_i_568_);
v___y_559_ = v___x_572_;
goto v___jp_558_;
}
v___jp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v___y_574_, v_fvarId_547_);
switch(lean_obj_tag(v___x_575_))
{
case 0:
{
lean_object* v_index_576_; lean_object* v_size_577_; lean_object* v___x_578_; 
v_index_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_index_576_);
lean_dec_ref_known(v___x_575_, 3);
v_size_577_ = lean_ctor_get(v___y_574_, 0);
lean_inc(v_size_577_);
v___x_578_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_574_, v_size_577_, v_index_576_, v_fvarId_547_, v___x_565_);
lean_dec(v_index_576_);
v___y_559_ = v___x_578_;
goto v___jp_558_;
}
case 1:
{
lean_object* v_index_579_; 
v_index_579_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_index_579_);
lean_dec_ref_known(v___x_575_, 1);
v___y_567_ = v___y_574_;
v_i_568_ = v_index_579_;
goto v___jp_566_;
}
default: 
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_574_, v___x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_index_582_; 
v_index_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_index_582_);
lean_dec_ref_known(v___x_581_, 1);
v___y_567_ = v___y_574_;
v_i_568_ = v_index_582_;
goto v___jp_566_;
}
else
{
lean_dec(v_fvarId_547_);
v___y_559_ = v___y_574_;
goto v___jp_558_;
}
}
}
}
v___jp_583_:
{
lean_object* v_size_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_size_586_ = lean_ctor_get(v___y_584_, 0);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_add(v_size_586_, v___x_587_);
v___x_589_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_584_, v___x_588_, v_i_585_, v_fvarId_547_, v___x_565_);
lean_dec(v_i_585_);
v___y_559_ = v___x_589_;
goto v___jp_558_;
}
v___jp_590_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_551_);
lean_dec_ref(v_vars_551_);
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_591_, v_fvarId_547_);
switch(lean_obj_tag(v___x_592_))
{
case 0:
{
lean_object* v_index_593_; lean_object* v_size_594_; lean_object* v___x_595_; 
v_index_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_index_593_);
lean_dec_ref_known(v___x_592_, 3);
v_size_594_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_size_594_);
v___x_595_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_591_, v_size_594_, v_index_593_, v_fvarId_547_, v___x_565_);
lean_dec(v_index_593_);
v___y_559_ = v___x_595_;
goto v___jp_558_;
}
case 1:
{
lean_object* v_index_596_; 
v_index_596_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_index_596_);
lean_dec_ref_known(v___x_592_, 1);
v___y_584_ = v___x_591_;
v_i_585_ = v_index_596_;
goto v___jp_583_;
}
default: 
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_591_, v___x_597_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_index_599_; 
v_index_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_index_599_);
lean_dec_ref_known(v___x_598_, 1);
v___y_584_ = v___x_591_;
v_i_585_ = v_index_599_;
goto v___jp_583_;
}
else
{
lean_dec(v_fvarId_547_);
v___y_559_ = v___x_591_;
goto v___jp_558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_628_, v_a_629_);
lean_dec(v_a_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_632_, v_a_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_IR_ToIR_bindErased(v_fvarId_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
return v_res_643_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_644_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_env_653_; lean_object* v_nextMacroScope_654_; lean_object* v_ngen_655_; lean_object* v_auxDeclNGen_656_; lean_object* v_traceState_657_; lean_object* v_messages_658_; lean_object* v_infoState_659_; lean_object* v_snapshotTasks_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_676_; 
v___x_652_ = lean_st_ref_take(v_a_650_);
v_env_653_ = lean_ctor_get(v___x_652_, 0);
v_nextMacroScope_654_ = lean_ctor_get(v___x_652_, 1);
v_ngen_655_ = lean_ctor_get(v___x_652_, 2);
v_auxDeclNGen_656_ = lean_ctor_get(v___x_652_, 3);
v_traceState_657_ = lean_ctor_get(v___x_652_, 4);
v_messages_658_ = lean_ctor_get(v___x_652_, 6);
v_infoState_659_ = lean_ctor_get(v___x_652_, 7);
v_snapshotTasks_660_ = lean_ctor_get(v___x_652_, 8);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_652_, 5);
lean_dec(v_unused_677_);
v___x_662_ = v___x_652_;
v_isShared_663_ = v_isSharedCheck_676_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snapshotTasks_660_);
lean_inc(v_infoState_659_);
lean_inc(v_messages_658_);
lean_inc(v_traceState_657_);
lean_inc(v_auxDeclNGen_656_);
lean_inc(v_ngen_655_);
lean_inc(v_nextMacroScope_654_);
lean_inc(v_env_653_);
lean_dec(v___x_652_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_676_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v_toEnvExtension_665_; lean_object* v_asyncMode_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_664_ = l_Lean_IR_declMapExt;
v_toEnvExtension_665_ = lean_ctor_get(v___x_664_, 0);
v_asyncMode_666_ = lean_ctor_get(v_toEnvExtension_665_, 2);
v___x_667_ = lean_box(0);
v___x_668_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_664_, v_env_653_, v_d_649_, v_asyncMode_666_, v___x_667_);
v___x_669_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 5, v___x_669_);
lean_ctor_set(v___x_662_, 0, v___x_668_);
v___x_671_ = v___x_662_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_nextMacroScope_654_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_ngen_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_auxDeclNGen_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_traceState_657_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_messages_658_);
lean_ctor_set(v_reuseFailAlloc_675_, 7, v_infoState_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 8, v_snapshotTasks_660_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_st_ref_put(v_a_650_, v___x_671_);
v___x_673_ = lean_box(0);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_678_, v_a_679_);
lean_dec(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_682_, v_a_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_IR_ToIR_addDecl(v_d_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_694_){
_start:
{
switch(lean_obj_tag(v_v_694_))
{
case 0:
{
lean_object* v_val_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_709_; 
v_val_695_ = lean_ctor_get(v_v_694_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_v_694_);
if (v_isSharedCheck_709_ == 0)
{
v___x_697_ = v_v_694_;
v_isShared_698_ = v_isSharedCheck_709_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_val_695_);
lean_dec(v_v_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_709_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___y_700_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_cstr_to_nat("4294967296");
v___x_706_ = lean_nat_dec_lt(v_val_695_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(8);
v___y_700_ = v___x_707_;
goto v___jp_699_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(12);
v___y_700_ = v___x_708_;
goto v___jp_699_;
}
v___jp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_698_ == 0)
{
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_val_695_);
v___x_702_ = v_reuseFailAlloc_704_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; 
lean_inc(v___y_700_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___y_700_);
return v___x_703_;
}
}
}
}
case 1:
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v_val_710_ = lean_ctor_get(v_v_694_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_v_694_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v_v_694_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v_v_694_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_val_710_);
v___x_715_ = v_reuseFailAlloc_718_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_box(7);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
return v___x_717_;
}
}
}
case 2:
{
uint8_t v_val_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_val_720_ = lean_ctor_get_uint8(v_v_694_, 0);
lean_dec_ref_known(v_v_694_, 0);
v___x_721_ = lean_uint8_to_nat(v_val_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_box(1);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
return v___x_724_;
}
case 3:
{
uint16_t v_val_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_val_725_ = lean_ctor_get_uint16(v_v_694_, 0);
lean_dec_ref_known(v_v_694_, 0);
v___x_726_ = lean_uint16_to_nat(v_val_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
v___x_728_ = lean_box(2);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
return v___x_729_;
}
case 4:
{
uint32_t v_val_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_val_730_ = lean_ctor_get_uint32(v_v_694_, 0);
lean_dec_ref_known(v_v_694_, 0);
v___x_731_ = lean_uint32_to_nat(v_val_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
v___x_733_ = lean_box(3);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
case 5:
{
uint64_t v_val_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_val_735_ = lean_ctor_get_uint64(v_v_694_, 0);
lean_dec_ref_known(v_v_694_, 0);
v___x_736_ = lean_uint64_to_nat(v_val_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
v___x_738_ = lean_box(4);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
return v___x_739_;
}
default: 
{
uint64_t v_val_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_val_740_ = lean_ctor_get_uint64(v_v_694_, 0);
lean_dec_ref_known(v_v_694_, 0);
v___x_741_ = lean_uint64_to_nat(v_val_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
v___x_743_ = lean_box(5);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
if (lean_obj_tag(v_a_745_) == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_box(1);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
else
{
lean_object* v_fvarId_750_; lean_object* v___x_751_; 
v_fvarId_750_ = lean_ctor_get(v_a_745_, 0);
v___x_751_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_750_, v_a_746_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec(v_a_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_756_, v_a_757_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_IR_ToIR_lowerArg(v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec(v_a_762_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_fvarId_771_; lean_object* v_type_772_; uint8_t v_borrow_773_; lean_object* v___x_774_; lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_788_; 
v_fvarId_771_ = lean_ctor_get(v_p_768_, 0);
lean_inc(v_fvarId_771_);
v_type_772_ = lean_ctor_get(v_p_768_, 2);
lean_inc_ref(v_type_772_);
v_borrow_773_ = lean_ctor_get_uint8(v_p_768_, sizeof(void*)*3);
lean_dec_ref(v_p_768_);
v___x_774_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_771_, v_a_769_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; uint8_t v___y_781_; 
v___x_779_ = l_Lean_IR_toIRType(v_type_772_);
lean_dec_ref(v_type_772_);
if (v_borrow_773_ == 0)
{
v___y_781_ = v_borrow_773_;
goto v___jp_780_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = l_Lean_IR_IRType_isScalar(v___x_779_);
if (v___x_786_ == 0)
{
v___y_781_ = v_borrow_773_;
goto v___jp_780_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = 0;
v___y_781_ = v___x_787_;
goto v___jp_780_;
}
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_782_, 0, v_a_775_);
lean_ctor_set(v___x_782_, 1, v___x_779_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*2, v___y_781_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_782_);
v___x_784_ = v___x_777_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_789_, v_a_790_);
lean_dec(v_a_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_793_, v_a_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_IR_ToIR_lowerParam(v_p_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_805_){
_start:
{
lean_object* v_name_806_; lean_object* v_cidx_807_; lean_object* v_size_808_; lean_object* v_usize_809_; lean_object* v_ssize_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_name_806_ = lean_ctor_get(v_i_805_, 0);
v_cidx_807_ = lean_ctor_get(v_i_805_, 1);
v_size_808_ = lean_ctor_get(v_i_805_, 2);
v_usize_809_ = lean_ctor_get(v_i_805_, 3);
v_ssize_810_ = lean_ctor_get(v_i_805_, 4);
v_isSharedCheck_817_ = !lean_is_exclusive(v_i_805_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v_i_805_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_ssize_810_);
lean_inc(v_usize_809_);
lean_inc(v_size_808_);
lean_inc(v_cidx_807_);
lean_inc(v_name_806_);
lean_dec(v_i_805_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_name_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_cidx_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_size_808_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_usize_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_ssize_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_instMonadEIO(lean_box(0));
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_toApplicative_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_860_; 
v___x_826_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_827_ = l_StateRefT_x27_instMonad___redArg(v___x_826_);
v_toApplicative_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v___x_827_, 1);
lean_dec(v_unused_861_);
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_860_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_toApplicative_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_860_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_toFunctor_832_; lean_object* v_toSeq_833_; lean_object* v_toSeqLeft_834_; lean_object* v_toSeqRight_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_858_; 
v_toFunctor_832_ = lean_ctor_get(v_toApplicative_828_, 0);
v_toSeq_833_ = lean_ctor_get(v_toApplicative_828_, 2);
v_toSeqLeft_834_ = lean_ctor_get(v_toApplicative_828_, 3);
v_toSeqRight_835_ = lean_ctor_get(v_toApplicative_828_, 4);
v_isSharedCheck_858_ = !lean_is_exclusive(v_toApplicative_828_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_toApplicative_828_, 1);
lean_dec(v_unused_859_);
v___x_837_ = v_toApplicative_828_;
v_isShared_838_ = v_isSharedCheck_858_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_toSeqRight_835_);
lean_inc(v_toSeqLeft_834_);
lean_inc(v_toSeq_833_);
lean_inc(v_toFunctor_832_);
lean_dec(v_toApplicative_828_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_858_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___x_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___x_848_; 
v___f_839_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_840_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_832_);
v___f_841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_841_, 0, v_toFunctor_832_);
v___f_842_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_842_, 0, v_toFunctor_832_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v___f_841_);
lean_ctor_set(v___x_843_, 1, v___f_842_);
v___f_844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_844_, 0, v_toSeqRight_835_);
v___f_845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_845_, 0, v_toSeqLeft_834_);
v___f_846_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_846_, 0, v_toSeq_833_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v___f_844_);
lean_ctor_set(v___x_837_, 3, v___f_845_);
lean_ctor_set(v___x_837_, 2, v___f_846_);
lean_ctor_set(v___x_837_, 1, v___f_839_);
lean_ctor_set(v___x_837_, 0, v___x_843_);
v___x_848_ = v___x_837_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___f_839_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v___f_846_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v___f_845_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v___f_844_);
v___x_848_ = v_reuseFailAlloc_857_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___f_840_);
lean_ctor_set(v___x_830_, 0, v___x_848_);
v___x_850_ = v___x_830_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___f_840_);
v___x_850_ = v_reuseFailAlloc_856_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_8618__overap_854_; lean_object* v___x_855_; 
v___x_851_ = l_StateRefT_x27_instMonad___redArg(v___x_850_);
v___x_852_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_853_ = l_instInhabitedOfMonad___redArg(v___x_851_, v___x_852_);
v___x_8618__overap_854_ = lean_panic_fn_borrowed(v___x_853_, v_msg_821_);
lean_dec(v___x_853_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc(v___y_822_);
v___x_855_ = lean_apply_4(v___x_8618__overap_854_, v___y_822_, v___y_823_, v___y_824_, lean_box(0));
return v___x_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_868_, size_t v_i_869_, lean_object* v_bs_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_869_, v_sz_868_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_bs_870_);
return v___x_874_;
}
else
{
lean_object* v_v_875_; lean_object* v___x_876_; 
v_v_875_ = lean_array_uget_borrowed(v_bs_870_, v_i_869_);
lean_inc(v_v_875_);
v___x_876_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_875_, v___y_871_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v_bs_x27_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_unsigned_to_nat(0u);
v_bs_x27_879_ = lean_array_uset(v_bs_870_, v_i_869_, v___x_878_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_869_, v___x_880_);
v___x_882_ = lean_array_uset(v_bs_x27_879_, v_i_869_, v_a_877_);
v_i_869_ = v___x_881_;
v_bs_870_ = v___x_882_;
goto _start;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_bs_870_);
v_a_884_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_876_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_876_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_bs_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_898_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_897_, v_i_boxed_898_, v_bs_894_, v___y_895_);
lean_dec(v___y_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_900_, size_t v_i_901_, lean_object* v_bs_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_bs_902_);
return v___x_906_;
}
else
{
lean_object* v_v_907_; lean_object* v___x_908_; 
v_v_907_ = lean_array_uget_borrowed(v_bs_902_, v_i_901_);
v___x_908_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_907_, v___y_903_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v_bs_x27_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = lean_unsigned_to_nat(0u);
v_bs_x27_911_ = lean_array_uset(v_bs_902_, v_i_901_, v___x_910_);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_901_, v___x_912_);
v___x_914_ = lean_array_uset(v_bs_x27_911_, v_i_901_, v_a_909_);
v_i_901_ = v___x_913_;
v_bs_902_ = v___x_914_;
goto _start;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_bs_902_);
v_a_916_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_908_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_908_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_bs_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
size_t v_sz_boxed_929_; size_t v_i_boxed_930_; lean_object* v_res_931_; 
v_sz_boxed_929_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_930_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_929_, v_i_boxed_930_, v_bs_926_, v___y_927_);
lean_dec(v___y_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_932_, lean_object* v_continueLet_933_, lean_object* v_var_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_939_, 0, v_i_932_);
lean_ctor_set(v___x_939_, 1, v_var_934_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
v___x_940_ = lean_apply_5(v_continueLet_933_, v___x_939_, v___y_935_, v___y_936_, v___y_937_, lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_941_, lean_object* v_continueLet_942_, lean_object* v_var_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_941_, v_continueLet_942_, v_var_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_949_, lean_object* v_offset_950_, lean_object* v_continueLet_951_, lean_object* v_var_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_957_, 0, v_n_949_);
lean_ctor_set(v___x_957_, 1, v_offset_950_);
lean_ctor_set(v___x_957_, 2, v_var_952_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
v___x_958_ = lean_apply_5(v_continueLet_951_, v___x_957_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_959_, lean_object* v_offset_960_, lean_object* v_continueLet_961_, lean_object* v_var_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_959_, v_offset_960_, v_continueLet_961_, v_var_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_968_, lean_object* v_continueLet_969_, lean_object* v_var_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v_n_968_);
lean_ctor_set(v___x_975_, 1, v_var_970_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
v___x_976_ = lean_apply_5(v_continueLet_969_, v___x_975_, v___y_971_, v___y_972_, v___y_973_, lean_box(0));
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_977_, lean_object* v_continueLet_978_, lean_object* v_var_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_977_, v_continueLet_978_, v_var_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_985_, lean_object* v_var_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_991_, 0, v_var_986_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
v___x_992_ = lean_apply_5(v_continueLet_985_, v___x_991_, v___y_987_, v___y_988_, v___y_989_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_993_, lean_object* v_var_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_993_, v_var_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_1000_, lean_object* v_continueLet_1001_, lean_object* v_var_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_i_1000_);
lean_ctor_set(v___x_1007_, 1, v_var_1002_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
v___x_1008_ = lean_apply_5(v_continueLet_1001_, v___x_1007_, v___y_1003_, v___y_1004_, v___y_1005_, lean_box(0));
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_1009_, lean_object* v_continueLet_1010_, lean_object* v_var_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_1009_, v_continueLet_1010_, v_var_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_1017_, lean_object* v_continueLet_1018_, lean_object* v_var_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = l_Lean_IR_toIRType(v_ty_1017_);
v___x_1025_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v_var_1019_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
v___x_1026_ = lean_apply_5(v_continueLet_1018_, v___x_1025_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_1027_, lean_object* v_continueLet_1028_, lean_object* v_var_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_1027_, v_continueLet_1028_, v_var_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v_ty_1027_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_1035_, lean_object* v_i_1036_, uint8_t v_updateHeader_1037_, lean_object* v_continueLet_1038_, lean_object* v_var_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_sz_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v_sz_1044_ = lean_array_size(v_args_1035_);
v___x_1045_ = ((size_t)0ULL);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1044_, v___x_1045_, v_args_1035_, v___y_1040_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v_name_1048_; lean_object* v_cidx_1049_; lean_object* v_size_1050_; lean_object* v_usize_1051_; lean_object* v_ssize_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_name_1048_ = lean_ctor_get(v_i_1036_, 0);
v_cidx_1049_ = lean_ctor_get(v_i_1036_, 1);
v_size_1050_ = lean_ctor_get(v_i_1036_, 2);
v_usize_1051_ = lean_ctor_get(v_i_1036_, 3);
v_ssize_1052_ = lean_ctor_get(v_i_1036_, 4);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_i_1036_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v_i_1036_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_ssize_1052_);
lean_inc(v_usize_1051_);
lean_inc(v_size_1050_);
lean_inc(v_cidx_1049_);
lean_inc(v_name_1048_);
lean_dec(v_i_1036_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_name_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_cidx_1049_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_size_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_usize_1051_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_ssize_1052_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_1058_, 0, v_var_1039_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
lean_ctor_set(v___x_1058_, 2, v_a_1047_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*3, v_updateHeader_1037_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
v___x_1059_ = lean_apply_5(v_continueLet_1038_, v___x_1058_, v___y_1040_, v___y_1041_, v___y_1042_, lean_box(0));
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_var_1039_);
lean_dec_ref(v_continueLet_1038_);
lean_dec_ref(v_i_1036_);
v_a_1062_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1046_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1046_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_1070_, lean_object* v_i_1071_, lean_object* v_updateHeader_1072_, lean_object* v_continueLet_1073_, lean_object* v_var_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v_updateHeader_9660__boxed_1079_; lean_object* v_res_1080_; 
v_updateHeader_9660__boxed_1079_ = lean_unbox(v_updateHeader_1072_);
v_res_1080_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_1070_, v_i_1071_, v_updateHeader_9660__boxed_1079_, v_continueLet_1073_, v_var_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_1081_, lean_object* v_var_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_var_1082_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
v___x_1088_ = lean_apply_5(v_continueLet_1081_, v___x_1087_, v___y_1083_, v___y_1084_, v___y_1085_, lean_box(0));
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_1089_, lean_object* v_var_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_1089_, v_var_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_1096_, lean_object* v_continueLet_1097_, lean_object* v_id_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
size_t v_sz_1103_; size_t v___x_1104_; lean_object* v___x_1105_; 
v_sz_1103_ = lean_array_size(v_args_1096_);
v___x_1104_ = ((size_t)0ULL);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1103_, v___x_1104_, v_args_1096_, v___y_1099_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_id_1098_);
lean_ctor_set(v___x_1107_, 1, v_a_1106_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
v___x_1108_ = lean_apply_5(v_continueLet_1097_, v___x_1107_, v___y_1099_, v___y_1100_, v___y_1101_, lean_box(0));
return v___x_1108_;
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_id_1098_);
lean_dec_ref(v_continueLet_1097_);
v_a_1109_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1105_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1105_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_1117_, lean_object* v_continueLet_1118_, lean_object* v_id_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_1117_, v_continueLet_1118_, v_id_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_1125_, lean_object* v_k_1126_, lean_object* v_type_1127_, lean_object* v_e_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_1125_, v___y_1129_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = l_Lean_IR_ToIR_lowerCode(v_k_1126_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1140_, 0, v_a_1134_);
lean_ctor_set(v___x_1140_, 1, v_type_1127_);
lean_ctor_set(v___x_1140_, 2, v_e_1128_);
lean_ctor_set(v___x_1140_, 3, v_a_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
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
else
{
lean_dec(v_a_1134_);
lean_dec_ref(v_e_1128_);
lean_dec(v_type_1127_);
return v___x_1135_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_e_1128_);
lean_dec(v_type_1127_);
lean_dec_ref(v_k_1126_);
v_a_1145_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1133_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1133_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_1153_, lean_object* v_k_1154_, lean_object* v_type_1155_, lean_object* v_e_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_1153_, v_k_1154_, v_type_1155_, v_e_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_1162_, lean_object* v_k_1163_, lean_object* v_fvarId_1164_, lean_object* v_f_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1164_, v_a_1166_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
if (lean_obj_tag(v_a_1171_) == 0)
{
lean_object* v_id_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v_k_1163_);
lean_dec_ref(v_decl_1162_);
v_id_1172_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_id_1172_);
lean_dec_ref_known(v_a_1171_, 1);
lean_inc(v_a_1168_);
lean_inc_ref(v_a_1167_);
lean_inc(v_a_1166_);
v___x_1173_ = lean_apply_5(v_f_1165_, v_id_1172_, v_a_1166_, v_a_1167_, v_a_1168_, lean_box(0));
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_dec_ref(v_f_1165_);
v___x_1174_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1162_, v_k_1163_, v_a_1166_, v_a_1167_, v_a_1168_);
return v___x_1174_;
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_f_1165_);
lean_dec_ref(v_k_1163_);
lean_dec_ref(v_decl_1162_);
v_a_1175_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1170_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1170_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_1183_, lean_object* v_k_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_fvarId_1189_; lean_object* v_type_1190_; lean_object* v_value_1191_; lean_object* v_type_1192_; lean_object* v_continueLet_1193_; 
v_fvarId_1189_ = lean_ctor_get(v_decl_1183_, 0);
v_type_1190_ = lean_ctor_get(v_decl_1183_, 2);
v_value_1191_ = lean_ctor_get(v_decl_1183_, 3);
lean_inc(v_value_1191_);
v_type_1192_ = l_Lean_IR_toIRType(v_type_1190_);
lean_inc(v_type_1192_);
lean_inc_ref(v_k_1184_);
lean_inc(v_fvarId_1189_);
v_continueLet_1193_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_1193_, 0, v_fvarId_1189_);
lean_closure_set(v_continueLet_1193_, 1, v_k_1184_);
lean_closure_set(v_continueLet_1193_, 2, v_type_1192_);
switch(lean_obj_tag(v_value_1191_))
{
case 0:
{
lean_object* v_value_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1204_; 
lean_inc(v_fvarId_1189_);
lean_dec_ref(v_continueLet_1193_);
lean_dec_ref(v_decl_1183_);
v_value_1194_ = lean_ctor_get(v_value_1191_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_value_1191_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1196_ = v_value_1191_;
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_value_1194_);
lean_dec(v_value_1191_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v_fst_1199_; lean_object* v___x_1201_; 
v___x_1198_ = l_Lean_IR_ToIR_lowerLitValue(v_value_1194_);
v_fst_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_fst_1199_);
lean_dec_ref(v___x_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 11);
lean_ctor_set(v___x_1196_, 0, v_fst_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_fst_1199_);
v___x_1201_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_1189_, v_k_1184_, v_type_1192_, v___x_1201_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1202_;
}
}
}
case 1:
{
lean_object* v___x_1205_; 
lean_dec_ref(v_continueLet_1193_);
lean_dec(v_type_1192_);
v___x_1205_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1183_, v_k_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1205_;
}
case 4:
{
lean_object* v_fvarId_1206_; lean_object* v_args_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
lean_dec(v_type_1192_);
v_fvarId_1206_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_fvarId_1206_);
v_args_1207_ = lean_ctor_get(v_value_1191_, 1);
lean_inc_ref(v_args_1207_);
lean_dec_ref_known(v_value_1191_, 2);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1208_, 0, v_args_1207_);
lean_closure_set(v___f_1208_, 1, v_continueLet_1193_);
v___x_1209_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_fvarId_1206_, v___f_1208_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_fvarId_1206_);
return v___x_1209_;
}
case 5:
{
lean_object* v_i_1210_; lean_object* v_args_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1243_; 
lean_inc(v_fvarId_1189_);
lean_dec_ref(v_continueLet_1193_);
lean_dec_ref(v_decl_1183_);
v_i_1210_ = lean_ctor_get(v_value_1191_, 0);
v_args_1211_ = lean_ctor_get(v_value_1191_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_value_1191_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1213_ = v_value_1191_;
v_isShared_1214_ = v_isSharedCheck_1243_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_args_1211_);
lean_inc(v_i_1210_);
lean_dec(v_value_1191_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1243_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
size_t v_sz_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v_sz_1215_ = lean_array_size(v_args_1211_);
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1215_, v___x_1216_, v_args_1211_, v_a_1185_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_name_1219_; lean_object* v_cidx_1220_; lean_object* v_size_1221_; lean_object* v_usize_1222_; lean_object* v_ssize_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1234_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v_name_1219_ = lean_ctor_get(v_i_1210_, 0);
v_cidx_1220_ = lean_ctor_get(v_i_1210_, 1);
v_size_1221_ = lean_ctor_get(v_i_1210_, 2);
v_usize_1222_ = lean_ctor_get(v_i_1210_, 3);
v_ssize_1223_ = lean_ctor_get(v_i_1210_, 4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_i_1210_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1225_ = v_i_1210_;
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_ssize_1223_);
lean_inc(v_usize_1222_);
lean_inc(v_size_1221_);
lean_inc(v_cidx_1220_);
lean_inc(v_name_1219_);
lean_dec(v_i_1210_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_name_1219_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_cidx_1220_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_size_1221_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_usize_1222_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_ssize_1223_);
v___x_1228_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 0);
lean_ctor_set(v___x_1213_, 1, v_a_1218_);
lean_ctor_set(v___x_1213_, 0, v___x_1228_);
v___x_1230_ = v___x_1213_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_a_1218_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_1189_, v_k_1184_, v_type_1192_, v___x_1230_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_del_object(v___x_1213_);
lean_dec_ref(v_i_1210_);
lean_dec(v_type_1192_);
lean_dec(v_fvarId_1189_);
lean_dec_ref(v_k_1184_);
v_a_1235_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1217_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1217_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1244_; lean_object* v_var_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
lean_dec(v_type_1192_);
v_i_1244_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_i_1244_);
v_var_1245_ = lean_ctor_get(v_value_1191_, 1);
lean_inc(v_var_1245_);
lean_dec_ref_known(v_value_1191_, 2);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1246_, 0, v_i_1244_);
lean_closure_set(v___f_1246_, 1, v_continueLet_1193_);
v___x_1247_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_var_1245_, v___f_1246_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_var_1245_);
return v___x_1247_;
}
case 7:
{
lean_object* v_i_1248_; lean_object* v_var_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; 
lean_dec(v_type_1192_);
v_i_1248_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_i_1248_);
v_var_1249_ = lean_ctor_get(v_value_1191_, 1);
lean_inc(v_var_1249_);
lean_dec_ref_known(v_value_1191_, 2);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1250_, 0, v_i_1248_);
lean_closure_set(v___f_1250_, 1, v_continueLet_1193_);
v___x_1251_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_var_1249_, v___f_1250_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_var_1249_);
return v___x_1251_;
}
case 8:
{
lean_object* v_n_1252_; lean_object* v_offset_1253_; lean_object* v_var_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; 
lean_dec(v_type_1192_);
v_n_1252_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_n_1252_);
v_offset_1253_ = lean_ctor_get(v_value_1191_, 1);
lean_inc(v_offset_1253_);
v_var_1254_ = lean_ctor_get(v_value_1191_, 2);
lean_inc(v_var_1254_);
lean_dec_ref_known(v_value_1191_, 3);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1255_, 0, v_n_1252_);
lean_closure_set(v___f_1255_, 1, v_offset_1253_);
lean_closure_set(v___f_1255_, 2, v_continueLet_1193_);
v___x_1256_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_var_1254_, v___f_1255_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_var_1254_);
return v___x_1256_;
}
case 9:
{
lean_object* v_fn_1257_; lean_object* v_args_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1278_; 
lean_inc(v_fvarId_1189_);
lean_dec_ref(v_continueLet_1193_);
lean_dec_ref(v_decl_1183_);
v_fn_1257_ = lean_ctor_get(v_value_1191_, 0);
v_args_1258_ = lean_ctor_get(v_value_1191_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_value_1191_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1260_ = v_value_1191_;
v_isShared_1261_ = v_isSharedCheck_1278_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_args_1258_);
lean_inc(v_fn_1257_);
lean_dec(v_value_1191_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1278_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
size_t v_sz_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v_sz_1262_ = lean_array_size(v_args_1258_);
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1262_, v___x_1263_, v_args_1258_, v_a_1185_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 6);
lean_ctor_set(v___x_1260_, 1, v_a_1265_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_fn_1257_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1265_);
v___x_1267_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_1189_, v_k_1184_, v_type_1192_, v___x_1267_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1268_;
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_del_object(v___x_1260_);
lean_dec(v_fn_1257_);
lean_dec(v_type_1192_);
lean_dec(v_fvarId_1189_);
lean_dec_ref(v_k_1184_);
v_a_1270_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1264_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1264_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1279_; lean_object* v_args_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1300_; 
lean_inc(v_fvarId_1189_);
lean_dec_ref(v_continueLet_1193_);
lean_dec_ref(v_decl_1183_);
v_fn_1279_ = lean_ctor_get(v_value_1191_, 0);
v_args_1280_ = lean_ctor_get(v_value_1191_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_value_1191_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1282_ = v_value_1191_;
v_isShared_1283_ = v_isSharedCheck_1300_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_args_1280_);
lean_inc(v_fn_1279_);
lean_dec(v_value_1191_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1300_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
size_t v_sz_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v_sz_1284_ = lean_array_size(v_args_1280_);
v___x_1285_ = ((size_t)0ULL);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1284_, v___x_1285_, v_args_1280_, v_a_1185_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 7);
lean_ctor_set(v___x_1282_, 1, v_a_1287_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_fn_1279_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_a_1287_);
v___x_1289_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_1189_, v_k_1184_, v_type_1192_, v___x_1289_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1290_;
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_del_object(v___x_1282_);
lean_dec(v_fn_1279_);
lean_dec(v_type_1192_);
lean_dec(v_fvarId_1189_);
lean_dec_ref(v_k_1184_);
v_a_1292_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1286_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1286_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1301_; lean_object* v_var_1302_; lean_object* v___f_1303_; lean_object* v___x_1304_; 
lean_dec(v_type_1192_);
v_n_1301_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_n_1301_);
v_var_1302_ = lean_ctor_get(v_value_1191_, 1);
lean_inc(v_var_1302_);
lean_dec_ref_known(v_value_1191_, 2);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1303_, 0, v_n_1301_);
lean_closure_set(v___f_1303_, 1, v_continueLet_1193_);
v___x_1304_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_var_1302_, v___f_1303_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_var_1302_);
return v___x_1304_;
}
case 12:
{
lean_object* v_var_1305_; lean_object* v_i_1306_; uint8_t v_updateHeader_1307_; lean_object* v_args_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; 
lean_dec(v_type_1192_);
v_var_1305_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_var_1305_);
v_i_1306_ = lean_ctor_get(v_value_1191_, 1);
lean_inc_ref(v_i_1306_);
v_updateHeader_1307_ = lean_ctor_get_uint8(v_value_1191_, sizeof(void*)*3);
v_args_1308_ = lean_ctor_get(v_value_1191_, 2);
lean_inc_ref(v_args_1308_);
lean_dec_ref_known(v_value_1191_, 3);
v___x_1309_ = lean_box(v_updateHeader_1307_);
v___f_1310_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1310_, 0, v_args_1308_);
lean_closure_set(v___f_1310_, 1, v_i_1306_);
lean_closure_set(v___f_1310_, 2, v___x_1309_);
lean_closure_set(v___f_1310_, 3, v_continueLet_1193_);
v___x_1311_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_var_1305_, v___f_1310_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_var_1305_);
return v___x_1311_;
}
case 13:
{
lean_object* v_ty_1312_; lean_object* v_fvarId_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; 
lean_dec(v_type_1192_);
v_ty_1312_ = lean_ctor_get(v_value_1191_, 0);
lean_inc_ref(v_ty_1312_);
v_fvarId_1313_ = lean_ctor_get(v_value_1191_, 1);
lean_inc(v_fvarId_1313_);
lean_dec_ref_known(v_value_1191_, 2);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1314_, 0, v_ty_1312_);
lean_closure_set(v___f_1314_, 1, v_continueLet_1193_);
v___x_1315_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_fvarId_1313_, v___f_1314_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_fvarId_1313_);
return v___x_1315_;
}
case 14:
{
lean_object* v_fvarId_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; 
lean_dec(v_type_1192_);
v_fvarId_1316_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_fvarId_1316_);
lean_dec_ref_known(v_value_1191_, 1);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1317_, 0, v_continueLet_1193_);
v___x_1318_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_fvarId_1316_, v___f_1317_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_fvarId_1316_);
return v___x_1318_;
}
default: 
{
lean_object* v_fvarId_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; 
lean_dec(v_type_1192_);
v_fvarId_1319_ = lean_ctor_get(v_value_1191_, 0);
lean_inc(v_fvarId_1319_);
lean_dec_ref_known(v_value_1191_, 1);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1320_, 0, v_continueLet_1193_);
v___x_1321_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1183_, v_k_1184_, v_fvarId_1319_, v___f_1320_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_fvarId_1319_);
return v___x_1321_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1325_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1326_ = lean_unsigned_to_nat(15u);
v___x_1327_ = lean_unsigned_to_nat(128u);
v___x_1328_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1329_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1330_ = l_mkPanicMessageWithDecl(v___x_1329_, v___x_1328_, v___x_1327_, v___x_1326_, v___x_1325_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
if (lean_obj_tag(v_a_1331_) == 1)
{
lean_object* v_info_1336_; lean_object* v_code_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1373_; 
v_info_1336_ = lean_ctor_get(v_a_1331_, 0);
v_code_1337_ = lean_ctor_get(v_a_1331_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_a_1331_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1339_ = v_a_1331_;
v_isShared_1340_ = v_isSharedCheck_1373_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_code_1337_);
lean_inc(v_info_1336_);
lean_dec(v_a_1331_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1373_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_IR_ToIR_lowerCode(v_code_1337_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1364_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1364_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1364_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_name_1346_; lean_object* v_cidx_1347_; lean_object* v_size_1348_; lean_object* v_usize_1349_; lean_object* v_ssize_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1363_; 
v_name_1346_ = lean_ctor_get(v_info_1336_, 0);
v_cidx_1347_ = lean_ctor_get(v_info_1336_, 1);
v_size_1348_ = lean_ctor_get(v_info_1336_, 2);
v_usize_1349_ = lean_ctor_get(v_info_1336_, 3);
v_ssize_1350_ = lean_ctor_get(v_info_1336_, 4);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_info_1336_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1352_ = v_info_1336_;
v_isShared_1353_ = v_isSharedCheck_1363_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_ssize_1350_);
lean_inc(v_usize_1349_);
lean_inc(v_size_1348_);
lean_inc(v_cidx_1347_);
lean_inc(v_name_1346_);
lean_dec(v_info_1336_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1363_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_name_1346_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_cidx_1347_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_size_1348_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_usize_1349_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_ssize_1350_);
v___x_1355_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 0);
lean_ctor_set(v___x_1339_, 1, v_a_1342_);
lean_ctor_set(v___x_1339_, 0, v___x_1355_);
v___x_1357_ = v___x_1339_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_a_1342_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1357_);
v___x_1359_ = v___x_1344_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
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
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1339_);
lean_dec_ref(v_info_1336_);
v_a_1365_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1341_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1341_);
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
else
{
lean_object* v_code_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1398_; 
v_code_1374_ = lean_ctor_get(v_a_1331_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_a_1331_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1376_ = v_a_1331_;
v_isShared_1377_ = v_isSharedCheck_1398_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_code_1374_);
lean_dec(v_a_1331_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1398_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_IR_ToIR_lowerCode(v_code_1374_, v_a_1332_, v_a_1333_, v_a_1334_);
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
lean_ctor_set_tag(v___x_1376_, 1);
lean_ctor_set(v___x_1376_, 0, v_a_1379_);
v___x_1384_ = v___x_1376_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1399_, size_t v_i_1400_, lean_object* v_bs_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_lt(v_i_1400_, v_sz_1399_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_bs_1401_);
return v___x_1407_;
}
else
{
lean_object* v_v_1408_; lean_object* v___x_1409_; 
v_v_1408_ = lean_array_uget_borrowed(v_bs_1401_, v_i_1400_);
lean_inc(v_v_1408_);
v___x_1409_ = l_Lean_IR_ToIR_lowerAlt(v_v_1408_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; lean_object* v_bs_x27_1412_; size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = lean_unsigned_to_nat(0u);
v_bs_x27_1412_ = lean_array_uset(v_bs_1401_, v_i_1400_, v___x_1411_);
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1400_, v___x_1413_);
v___x_1415_ = lean_array_uset(v_bs_x27_1412_, v_i_1400_, v_a_1410_);
v_i_1400_ = v___x_1414_;
v_bs_1401_ = v___x_1415_;
goto _start;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_bs_1401_);
v_a_1417_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1409_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1409_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
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
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1426_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1427_ = lean_unsigned_to_nat(53u);
v___x_1428_ = lean_unsigned_to_nat(95u);
v___x_1429_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1430_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1431_ = l_mkPanicMessageWithDecl(v___x_1430_, v___x_1429_, v___x_1428_, v___x_1427_, v___x_1426_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1432_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1433_ = lean_unsigned_to_nat(44u);
v___x_1434_ = lean_unsigned_to_nat(106u);
v___x_1435_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1436_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1437_ = l_mkPanicMessageWithDecl(v___x_1436_, v___x_1435_, v___x_1434_, v___x_1433_, v___x_1432_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1438_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1439_ = lean_unsigned_to_nat(44u);
v___x_1440_ = lean_unsigned_to_nat(114u);
v___x_1441_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1442_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1443_ = l_mkPanicMessageWithDecl(v___x_1442_, v___x_1441_, v___x_1440_, v___x_1439_, v___x_1438_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1444_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1445_ = lean_unsigned_to_nat(34u);
v___x_1446_ = lean_unsigned_to_nat(113u);
v___x_1447_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1448_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1449_ = l_mkPanicMessageWithDecl(v___x_1448_, v___x_1447_, v___x_1446_, v___x_1445_, v___x_1444_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1450_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1451_ = lean_unsigned_to_nat(44u);
v___x_1452_ = lean_unsigned_to_nat(110u);
v___x_1453_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1454_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1455_ = l_mkPanicMessageWithDecl(v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1456_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1457_ = lean_unsigned_to_nat(34u);
v___x_1458_ = lean_unsigned_to_nat(109u);
v___x_1459_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1460_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1461_ = l_mkPanicMessageWithDecl(v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_, v___x_1456_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1462_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1463_ = lean_unsigned_to_nat(41u);
v___x_1464_ = lean_unsigned_to_nat(117u);
v___x_1465_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1466_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1467_ = l_mkPanicMessageWithDecl(v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1468_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1469_ = lean_unsigned_to_nat(41u);
v___x_1470_ = lean_unsigned_to_nat(120u);
v___x_1471_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1472_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1473_ = l_mkPanicMessageWithDecl(v___x_1472_, v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1474_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1475_ = lean_unsigned_to_nat(41u);
v___x_1476_ = lean_unsigned_to_nat(123u);
v___x_1477_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1478_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1479_ = l_mkPanicMessageWithDecl(v___x_1478_, v___x_1477_, v___x_1476_, v___x_1475_, v___x_1474_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1480_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1481_ = lean_unsigned_to_nat(41u);
v___x_1482_ = lean_unsigned_to_nat(126u);
v___x_1483_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1484_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1485_ = l_mkPanicMessageWithDecl(v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_, v___x_1480_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
switch(lean_obj_tag(v_c_1486_))
{
case 0:
{
lean_object* v_decl_1491_; lean_object* v_k_1492_; lean_object* v___x_1493_; 
v_decl_1491_ = lean_ctor_get(v_c_1486_, 0);
lean_inc_ref(v_decl_1491_);
v_k_1492_ = lean_ctor_get(v_c_1486_, 1);
lean_inc_ref(v_k_1492_);
lean_dec_ref_known(v_c_1486_, 2);
v___x_1493_ = l_Lean_IR_ToIR_lowerLet(v_decl_1491_, v_k_1492_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1493_;
}
case 1:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec_ref_known(v_c_1486_, 2);
v___x_1494_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1495_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1494_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1495_;
}
case 2:
{
lean_object* v_decl_1496_; lean_object* v_k_1497_; lean_object* v_fvarId_1498_; lean_object* v_params_1499_; lean_object* v_value_1500_; lean_object* v___x_1501_; 
v_decl_1496_ = lean_ctor_get(v_c_1486_, 0);
lean_inc_ref(v_decl_1496_);
v_k_1497_ = lean_ctor_get(v_c_1486_, 1);
lean_inc_ref(v_k_1497_);
lean_dec_ref_known(v_c_1486_, 2);
v_fvarId_1498_ = lean_ctor_get(v_decl_1496_, 0);
lean_inc(v_fvarId_1498_);
v_params_1499_ = lean_ctor_get(v_decl_1496_, 2);
lean_inc_ref(v_params_1499_);
v_value_1500_ = lean_ctor_get(v_decl_1496_, 4);
lean_inc_ref(v_value_1500_);
lean_dec_ref(v_decl_1496_);
v___x_1501_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1498_, v_a_1487_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; size_t v_sz_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v_sz_1503_ = lean_array_size(v_params_1499_);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1503_, v___x_1504_, v_params_1499_, v_a_1487_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = l_Lean_IR_ToIR_lowerCode(v_value_1500_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1509_ = l_Lean_IR_ToIR_lowerCode(v_k_1497_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1502_);
lean_ctor_set(v___x_1514_, 1, v_a_1506_);
lean_ctor_set(v___x_1514_, 2, v_a_1508_);
lean_ctor_set(v___x_1514_, 3, v_a_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_dec(v_a_1508_);
lean_dec(v_a_1506_);
lean_dec(v_a_1502_);
return v___x_1509_;
}
}
else
{
lean_dec(v_a_1506_);
lean_dec(v_a_1502_);
lean_dec_ref(v_k_1497_);
return v___x_1507_;
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1502_);
lean_dec_ref(v_value_1500_);
lean_dec_ref(v_k_1497_);
v_a_1519_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1505_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1505_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_value_1500_);
lean_dec_ref(v_params_1499_);
lean_dec_ref(v_k_1497_);
v_a_1527_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1501_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1501_);
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
case 3:
{
lean_object* v_fvarId_1535_; lean_object* v_args_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1572_; 
v_fvarId_1535_ = lean_ctor_get(v_c_1486_, 0);
v_args_1536_ = lean_ctor_get(v_c_1486_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1538_ = v_c_1486_;
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_args_1536_);
lean_inc(v_fvarId_1535_);
lean_dec(v_c_1486_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1535_, v_a_1487_);
lean_dec(v_fvarId_1535_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; size_t v_sz_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v_sz_1542_ = lean_array_size(v_args_1536_);
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1542_, v___x_1543_, v_args_1536_, v_a_1487_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1555_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 11);
lean_ctor_set(v___x_1538_, 1, v_a_1545_);
lean_ctor_set(v___x_1538_, 0, v_a_1541_);
v___x_1550_ = v___x_1538_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1541_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1541_);
lean_del_object(v___x_1538_);
v_a_1556_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1544_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1544_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1538_);
lean_dec_ref(v_args_1536_);
v_a_1564_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1540_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1540_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1573_; lean_object* v_typeName_1574_; lean_object* v_discr_1575_; lean_object* v_alts_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1616_; 
v_cases_1573_ = lean_ctor_get(v_c_1486_, 0);
lean_inc_ref(v_cases_1573_);
lean_dec_ref_known(v_c_1486_, 1);
v_typeName_1574_ = lean_ctor_get(v_cases_1573_, 0);
v_discr_1575_ = lean_ctor_get(v_cases_1573_, 2);
v_alts_1576_ = lean_ctor_get(v_cases_1573_, 3);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_cases_1573_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v_cases_1573_, 1);
lean_dec(v_unused_1617_);
v___x_1578_ = v_cases_1573_;
v_isShared_1579_ = v_isSharedCheck_1616_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_alts_1576_);
lean_inc(v_discr_1575_);
lean_inc(v_typeName_1574_);
lean_dec(v_cases_1573_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1616_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1575_, v_a_1487_);
lean_dec(v_discr_1575_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 0)
{
lean_object* v_id_1582_; size_t v_sz_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v_id_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_id_1582_);
lean_dec_ref_known(v_a_1581_, 1);
v_sz_1583_ = lean_array_size(v_alts_1576_);
v___x_1584_ = ((size_t)0ULL);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1583_, v___x_1584_, v_alts_1576_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1597_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = l_Lean_IR_nameToIRType(v_typeName_1574_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 9);
lean_ctor_set(v___x_1578_, 3, v_a_1586_);
lean_ctor_set(v___x_1578_, 2, v___x_1590_);
lean_ctor_set(v___x_1578_, 1, v_id_1582_);
v___x_1592_ = v___x_1578_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_typeName_1574_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_id_1582_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_a_1586_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1592_);
v___x_1594_ = v___x_1588_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_id_1582_);
lean_del_object(v___x_1578_);
lean_dec(v_typeName_1574_);
v_a_1598_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1585_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1585_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_a_1581_);
lean_del_object(v___x_1578_);
lean_dec_ref(v_alts_1576_);
lean_dec(v_typeName_1574_);
v___x_1606_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1607_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1606_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1607_;
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_del_object(v___x_1578_);
lean_dec_ref(v_alts_1576_);
lean_dec(v_typeName_1574_);
v_a_1608_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1580_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1580_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1642_; 
v_fvarId_1618_ = lean_ctor_get(v_c_1486_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1620_ = v_c_1486_;
v_isShared_1621_ = v_isSharedCheck_1642_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_fvarId_1618_);
lean_dec(v_c_1486_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1642_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1618_, v_a_1487_);
lean_dec(v_fvarId_1618_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1633_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1633_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1633_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 10);
lean_ctor_set(v___x_1620_, 0, v_a_1623_);
v___x_1628_ = v___x_1620_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1630_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1628_);
v___x_1630_ = v___x_1625_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_del_object(v___x_1620_);
v_a_1634_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1622_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1622_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v_c_1486_, 0);
lean_dec(v_unused_1651_);
v___x_1644_ = v_c_1486_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_c_1486_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_box(12);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
case 7:
{
lean_object* v_fvarId_1652_; lean_object* v_i_1653_; lean_object* v_y_1654_; lean_object* v_k_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1694_; 
v_fvarId_1652_ = lean_ctor_get(v_c_1486_, 0);
v_i_1653_ = lean_ctor_get(v_c_1486_, 1);
v_y_1654_ = lean_ctor_get(v_c_1486_, 2);
v_k_1655_ = lean_ctor_get(v_c_1486_, 3);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1657_ = v_c_1486_;
v_isShared_1658_ = v_isSharedCheck_1694_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_k_1655_);
lean_inc(v_y_1654_);
lean_inc(v_i_1653_);
lean_inc(v_fvarId_1652_);
lean_dec(v_c_1486_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1694_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1654_, v_a_1487_);
lean_dec(v_y_1654_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1652_, v_a_1487_);
lean_dec(v_fvarId_1652_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
if (lean_obj_tag(v_a_1662_) == 0)
{
lean_object* v_id_1663_; lean_object* v___x_1664_; 
v_id_1663_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_id_1663_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1664_ = l_Lean_IR_ToIR_lowerCode(v_k_1655_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1675_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 2);
lean_ctor_set(v___x_1657_, 3, v_a_1665_);
lean_ctor_set(v___x_1657_, 2, v_a_1660_);
lean_ctor_set(v___x_1657_, 0, v_id_1663_);
v___x_1670_ = v___x_1657_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_id_1663_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_i_1653_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_a_1660_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_dec(v_id_1663_);
lean_dec(v_a_1660_);
lean_del_object(v___x_1657_);
lean_dec(v_i_1653_);
return v___x_1664_;
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v_a_1662_);
lean_dec(v_a_1660_);
lean_del_object(v___x_1657_);
lean_dec_ref(v_k_1655_);
lean_dec(v_i_1653_);
v___x_1676_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1677_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1676_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1677_;
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1660_);
lean_del_object(v___x_1657_);
lean_dec_ref(v_k_1655_);
lean_dec(v_i_1653_);
v_a_1678_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1661_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1661_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_del_object(v___x_1657_);
lean_dec_ref(v_k_1655_);
lean_dec(v_i_1653_);
lean_dec(v_fvarId_1652_);
v_a_1686_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1659_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1659_);
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
case 8:
{
lean_object* v_fvarId_1695_; lean_object* v_i_1696_; lean_object* v_y_1697_; lean_object* v_k_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1740_; 
v_fvarId_1695_ = lean_ctor_get(v_c_1486_, 0);
v_i_1696_ = lean_ctor_get(v_c_1486_, 1);
v_y_1697_ = lean_ctor_get(v_c_1486_, 2);
v_k_1698_ = lean_ctor_get(v_c_1486_, 3);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1700_ = v_c_1486_;
v_isShared_1701_ = v_isSharedCheck_1740_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_k_1698_);
lean_inc(v_y_1697_);
lean_inc(v_i_1696_);
lean_inc(v_fvarId_1695_);
lean_dec(v_c_1486_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1740_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1697_, v_a_1487_);
lean_dec(v_y_1697_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
if (lean_obj_tag(v_a_1703_) == 0)
{
lean_object* v_id_1704_; lean_object* v___x_1705_; 
v_id_1704_ = lean_ctor_get(v_a_1703_, 0);
lean_inc(v_id_1704_);
lean_dec_ref_known(v_a_1703_, 1);
v___x_1705_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1695_, v_a_1487_);
lean_dec(v_fvarId_1695_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
if (lean_obj_tag(v_a_1706_) == 0)
{
lean_object* v_id_1707_; lean_object* v___x_1708_; 
v_id_1707_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_id_1707_);
lean_dec_ref_known(v_a_1706_, 1);
v___x_1708_ = l_Lean_IR_ToIR_lowerCode(v_k_1698_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1719_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1719_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1719_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 4);
lean_ctor_set(v___x_1700_, 3, v_a_1709_);
lean_ctor_set(v___x_1700_, 2, v_id_1704_);
lean_ctor_set(v___x_1700_, 0, v_id_1707_);
v___x_1714_ = v___x_1700_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_id_1707_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_i_1696_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_id_1704_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_dec(v_id_1707_);
lean_dec(v_id_1704_);
lean_del_object(v___x_1700_);
lean_dec(v_i_1696_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec(v_a_1706_);
lean_dec(v_id_1704_);
lean_del_object(v___x_1700_);
lean_dec_ref(v_k_1698_);
lean_dec(v_i_1696_);
v___x_1720_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1721_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1720_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1721_;
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_id_1704_);
lean_del_object(v___x_1700_);
lean_dec_ref(v_k_1698_);
lean_dec(v_i_1696_);
v_a_1722_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1705_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1705_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_a_1703_);
lean_del_object(v___x_1700_);
lean_dec_ref(v_k_1698_);
lean_dec(v_i_1696_);
lean_dec(v_fvarId_1695_);
v___x_1730_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1731_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1730_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1731_;
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_del_object(v___x_1700_);
lean_dec_ref(v_k_1698_);
lean_dec(v_i_1696_);
lean_dec(v_fvarId_1695_);
v_a_1732_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1702_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1702_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1741_; lean_object* v_i_1742_; lean_object* v_offset_1743_; lean_object* v_y_1744_; lean_object* v_ty_1745_; lean_object* v_k_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1789_; 
v_fvarId_1741_ = lean_ctor_get(v_c_1486_, 0);
v_i_1742_ = lean_ctor_get(v_c_1486_, 1);
v_offset_1743_ = lean_ctor_get(v_c_1486_, 2);
v_y_1744_ = lean_ctor_get(v_c_1486_, 3);
v_ty_1745_ = lean_ctor_get(v_c_1486_, 4);
v_k_1746_ = lean_ctor_get(v_c_1486_, 5);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1748_ = v_c_1486_;
v_isShared_1749_ = v_isSharedCheck_1789_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_k_1746_);
lean_inc(v_ty_1745_);
lean_inc(v_y_1744_);
lean_inc(v_offset_1743_);
lean_inc(v_i_1742_);
lean_inc(v_fvarId_1741_);
lean_dec(v_c_1486_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1789_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1744_, v_a_1487_);
lean_dec(v_y_1744_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
if (lean_obj_tag(v_a_1751_) == 0)
{
lean_object* v_id_1752_; lean_object* v___x_1753_; 
v_id_1752_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_id_1752_);
lean_dec_ref_known(v_a_1751_, 1);
v___x_1753_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1741_, v_a_1487_);
lean_dec(v_fvarId_1741_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
if (lean_obj_tag(v_a_1754_) == 0)
{
lean_object* v_id_1755_; lean_object* v___x_1756_; 
v_id_1755_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_id_1755_);
lean_dec_ref_known(v_a_1754_, 1);
v___x_1756_ = l_Lean_IR_ToIR_lowerCode(v_k_1746_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1768_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1768_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1768_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = l_Lean_IR_toIRType(v_ty_1745_);
lean_dec_ref(v_ty_1745_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 5);
lean_ctor_set(v___x_1748_, 5, v_a_1757_);
lean_ctor_set(v___x_1748_, 4, v___x_1761_);
lean_ctor_set(v___x_1748_, 3, v_id_1752_);
lean_ctor_set(v___x_1748_, 0, v_id_1755_);
v___x_1763_ = v___x_1748_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_id_1755_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_i_1742_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_offset_1743_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_id_1752_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v_a_1757_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1763_);
v___x_1765_ = v___x_1759_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_dec(v_id_1755_);
lean_dec(v_id_1752_);
lean_del_object(v___x_1748_);
lean_dec_ref(v_ty_1745_);
lean_dec(v_offset_1743_);
lean_dec(v_i_1742_);
return v___x_1756_;
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v_a_1754_);
lean_dec(v_id_1752_);
lean_del_object(v___x_1748_);
lean_dec_ref(v_k_1746_);
lean_dec_ref(v_ty_1745_);
lean_dec(v_offset_1743_);
lean_dec(v_i_1742_);
v___x_1769_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1770_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1769_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1770_;
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_id_1752_);
lean_del_object(v___x_1748_);
lean_dec_ref(v_k_1746_);
lean_dec_ref(v_ty_1745_);
lean_dec(v_offset_1743_);
lean_dec(v_i_1742_);
v_a_1771_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1753_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1753_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_a_1751_);
lean_del_object(v___x_1748_);
lean_dec_ref(v_k_1746_);
lean_dec_ref(v_ty_1745_);
lean_dec(v_offset_1743_);
lean_dec(v_i_1742_);
lean_dec(v_fvarId_1741_);
v___x_1779_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1780_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1779_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1780_;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1748_);
lean_dec_ref(v_k_1746_);
lean_dec_ref(v_ty_1745_);
lean_dec(v_offset_1743_);
lean_dec(v_i_1742_);
lean_dec(v_fvarId_1741_);
v_a_1781_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1750_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1750_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1790_; lean_object* v_cidx_1791_; lean_object* v_k_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1821_; 
v_fvarId_1790_ = lean_ctor_get(v_c_1486_, 0);
v_cidx_1791_ = lean_ctor_get(v_c_1486_, 1);
v_k_1792_ = lean_ctor_get(v_c_1486_, 2);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1794_ = v_c_1486_;
v_isShared_1795_ = v_isSharedCheck_1821_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_k_1792_);
lean_inc(v_cidx_1791_);
lean_inc(v_fvarId_1790_);
lean_dec(v_c_1486_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1821_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1790_, v_a_1487_);
lean_dec(v_fvarId_1790_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
if (lean_obj_tag(v_a_1797_) == 0)
{
lean_object* v_id_1798_; lean_object* v___x_1799_; 
v_id_1798_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_id_1798_);
lean_dec_ref_known(v_a_1797_, 1);
v___x_1799_ = l_Lean_IR_ToIR_lowerCode(v_k_1792_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 3);
lean_ctor_set(v___x_1794_, 2, v_a_1800_);
lean_ctor_set(v___x_1794_, 0, v_id_1798_);
v___x_1805_ = v___x_1794_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_id_1798_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_cidx_1791_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1805_);
v___x_1807_ = v___x_1802_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_dec(v_id_1798_);
lean_del_object(v___x_1794_);
lean_dec(v_cidx_1791_);
return v___x_1799_;
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec(v_a_1797_);
lean_del_object(v___x_1794_);
lean_dec_ref(v_k_1792_);
lean_dec(v_cidx_1791_);
v___x_1811_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1812_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1811_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1812_;
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_del_object(v___x_1794_);
lean_dec_ref(v_k_1792_);
lean_dec(v_cidx_1791_);
v_a_1813_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1796_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1796_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1822_; lean_object* v_n_1823_; uint8_t v_check_1824_; uint8_t v_persistent_1825_; lean_object* v_k_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1855_; 
v_fvarId_1822_ = lean_ctor_get(v_c_1486_, 0);
v_n_1823_ = lean_ctor_get(v_c_1486_, 1);
v_check_1824_ = lean_ctor_get_uint8(v_c_1486_, sizeof(void*)*3);
v_persistent_1825_ = lean_ctor_get_uint8(v_c_1486_, sizeof(void*)*3 + 1);
v_k_1826_ = lean_ctor_get(v_c_1486_, 2);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1828_ = v_c_1486_;
v_isShared_1829_ = v_isSharedCheck_1855_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_k_1826_);
lean_inc(v_n_1823_);
lean_inc(v_fvarId_1822_);
lean_dec(v_c_1486_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1855_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1822_, v_a_1487_);
lean_dec(v_fvarId_1822_);
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
v___x_1833_ = l_Lean_IR_ToIR_lowerCode(v_k_1826_, v_a_1487_, v_a_1488_, v_a_1489_);
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
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 6);
lean_ctor_set(v___x_1828_, 2, v_a_1834_);
lean_ctor_set(v___x_1828_, 0, v_id_1832_);
v___x_1839_ = v___x_1828_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_id_1832_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_n_1823_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_a_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*3, v_check_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*3 + 1, v_persistent_1825_);
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
lean_del_object(v___x_1828_);
lean_dec(v_n_1823_);
return v___x_1833_;
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_a_1831_);
lean_del_object(v___x_1828_);
lean_dec_ref(v_k_1826_);
lean_dec(v_n_1823_);
v___x_1845_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1846_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1845_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1846_;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_del_object(v___x_1828_);
lean_dec_ref(v_k_1826_);
lean_dec(v_n_1823_);
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
}
case 12:
{
lean_object* v_fvarId_1856_; lean_object* v_n_1857_; uint8_t v_check_1858_; uint8_t v_persistent_1859_; lean_object* v_k_1860_; lean_object* v___x_1861_; 
v_fvarId_1856_ = lean_ctor_get(v_c_1486_, 0);
lean_inc(v_fvarId_1856_);
v_n_1857_ = lean_ctor_get(v_c_1486_, 1);
lean_inc(v_n_1857_);
v_check_1858_ = lean_ctor_get_uint8(v_c_1486_, sizeof(void*)*4);
v_persistent_1859_ = lean_ctor_get_uint8(v_c_1486_, sizeof(void*)*4 + 1);
v_k_1860_ = lean_ctor_get(v_c_1486_, 3);
lean_inc_ref(v_k_1860_);
lean_dec_ref_known(v_c_1486_, 4);
v___x_1861_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1856_, v_a_1487_);
lean_dec(v_fvarId_1856_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
if (lean_obj_tag(v_a_1862_) == 0)
{
lean_object* v_id_1863_; lean_object* v___x_1864_; 
v_id_1863_ = lean_ctor_get(v_a_1862_, 0);
lean_inc(v_id_1863_);
lean_dec_ref_known(v_a_1862_, 1);
v___x_1864_ = l_Lean_IR_ToIR_lowerCode(v_k_1860_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v___x_1869_, 0, v_id_1863_);
lean_ctor_set(v___x_1869_, 1, v_n_1857_);
lean_ctor_set(v___x_1869_, 2, v_a_1865_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*3, v_check_1858_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*3 + 1, v_persistent_1859_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
else
{
lean_dec(v_id_1863_);
lean_dec(v_n_1857_);
return v___x_1864_;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_a_1862_);
lean_dec_ref(v_k_1860_);
lean_dec(v_n_1857_);
v___x_1874_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1875_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1874_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1875_;
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_k_1860_);
lean_dec(v_n_1857_);
v_a_1876_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1861_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1861_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
default: 
{
lean_object* v_fvarId_1884_; lean_object* v_k_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1914_; 
v_fvarId_1884_ = lean_ctor_get(v_c_1486_, 0);
v_k_1885_ = lean_ctor_get(v_c_1486_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_c_1486_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1887_ = v_c_1486_;
v_isShared_1888_ = v_isSharedCheck_1914_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_k_1885_);
lean_inc(v_fvarId_1884_);
lean_dec(v_c_1486_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1914_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1884_, v_a_1487_);
lean_dec(v_fvarId_1884_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
if (lean_obj_tag(v_a_1890_) == 0)
{
lean_object* v_id_1891_; lean_object* v___x_1892_; 
v_id_1891_ = lean_ctor_get(v_a_1890_, 0);
lean_inc(v_id_1891_);
lean_dec_ref_known(v_a_1890_, 1);
v___x_1892_ = l_Lean_IR_ToIR_lowerCode(v_k_1885_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1903_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1903_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1903_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 8);
lean_ctor_set(v___x_1887_, 1, v_a_1893_);
lean_ctor_set(v___x_1887_, 0, v_id_1891_);
v___x_1898_ = v___x_1887_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_id_1891_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
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
else
{
lean_dec(v_id_1891_);
lean_del_object(v___x_1887_);
return v___x_1892_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec(v_a_1890_);
lean_del_object(v___x_1887_);
lean_dec_ref(v_k_1885_);
v___x_1904_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1905_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1904_, v_a_1487_, v_a_1488_, v_a_1489_);
return v___x_1905_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1887_);
lean_dec_ref(v_k_1885_);
v_a_1906_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1889_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1889_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1915_, lean_object* v_k_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_fvarId_1921_; lean_object* v___x_1922_; 
v_fvarId_1921_ = lean_ctor_get(v_decl_1915_, 0);
lean_inc(v_fvarId_1921_);
lean_dec_ref(v_decl_1915_);
v___x_1922_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1921_, v_a_1917_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref_known(v___x_1922_, 1);
v___x_1923_ = l_Lean_IR_ToIR_lowerCode(v_k_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
return v___x_1923_;
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_k_1916_);
v_a_1924_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1922_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1922_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1932_, lean_object* v_k_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1932_, v_k_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1939_, lean_object* v_k_1940_, lean_object* v_fvarId_1941_, lean_object* v_f_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1939_, v_k_1940_, v_fvarId_1941_, v_f_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec(v_fvarId_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1948_, lean_object* v_i_1949_, lean_object* v_bs_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
size_t v_sz_boxed_1955_; size_t v_i_boxed_1956_; lean_object* v_res_1957_; 
v_sz_boxed_1955_ = lean_unbox_usize(v_sz_1948_);
lean_dec(v_sz_1948_);
v_i_boxed_1956_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1955_, v_i_boxed_1956_, v_bs_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_IR_ToIR_lowerAlt(v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1964_, lean_object* v_k_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_IR_ToIR_lowerLet(v_decl_1964_, v_k_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_IR_ToIR_lowerCode(v_c_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1977_, lean_object* v_k_1978_, lean_object* v_x_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1977_, v_k_1978_, v_a_1980_, v_a_1981_, v_a_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1985_, lean_object* v_k_1986_, lean_object* v_x_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1985_, v_k_1986_, v_x_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1993_, size_t v_i_1994_, lean_object* v_bs_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1993_, v_i_1994_, v_bs_1995_, v___y_1996_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_2001_, lean_object* v_i_2002_, lean_object* v_bs_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
size_t v_sz_boxed_2008_; size_t v_i_boxed_2009_; lean_object* v_res_2010_; 
v_sz_boxed_2008_ = lean_unbox_usize(v_sz_2001_);
lean_dec(v_sz_2001_);
v_i_boxed_2009_ = lean_unbox_usize(v_i_2002_);
lean_dec(v_i_2002_);
v_res_2010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_2008_, v_i_boxed_2009_, v_bs_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_bs_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2011_, v_i_2012_, v_bs_2013_, v___y_2014_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_2019_, lean_object* v_i_2020_, lean_object* v_bs_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
size_t v_sz_boxed_2026_; size_t v_i_boxed_2027_; lean_object* v_res_2028_; 
v_sz_boxed_2026_ = lean_unbox_usize(v_sz_2019_);
lean_dec(v_sz_2019_);
v_i_boxed_2027_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_2026_, v_i_boxed_2027_, v_bs_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_toSignature_2034_; lean_object* v_value_2035_; lean_object* v_name_2036_; lean_object* v_type_2037_; lean_object* v_params_2038_; size_t v_sz_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v_toSignature_2034_ = lean_ctor_get(v_d_2029_, 0);
lean_inc_ref(v_toSignature_2034_);
v_value_2035_ = lean_ctor_get(v_d_2029_, 1);
lean_inc_ref(v_value_2035_);
lean_dec_ref(v_d_2029_);
v_name_2036_ = lean_ctor_get(v_toSignature_2034_, 0);
lean_inc(v_name_2036_);
v_type_2037_ = lean_ctor_get(v_toSignature_2034_, 2);
lean_inc_ref(v_type_2037_);
v_params_2038_ = lean_ctor_get(v_toSignature_2034_, 3);
lean_inc_ref(v_params_2038_);
lean_dec_ref(v_toSignature_2034_);
v_sz_2039_ = lean_array_size(v_params_2038_);
v___x_2040_ = ((size_t)0ULL);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_2039_, v___x_2040_, v_params_2038_, v_a_2030_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2098_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2098_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2098_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_IR_toIRType(v_type_2037_);
lean_dec_ref(v_type_2037_);
if (lean_obj_tag(v_value_2035_) == 0)
{
lean_object* v_code_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_2044_);
v_code_2047_ = lean_ctor_get(v_value_2035_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_value_2035_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2049_ = v_value_2035_;
v_isShared_2050_ = v_isSharedCheck_2073_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_code_2047_);
lean_dec(v_value_2035_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2073_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_IR_ToIR_lowerCode(v_code_2047_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2064_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2057_, 0, v_name_2036_);
lean_ctor_set(v___x_2057_, 1, v_a_2042_);
lean_ctor_set(v___x_2057_, 2, v___x_2046_);
lean_ctor_set(v___x_2057_, 3, v_a_2052_);
lean_ctor_set(v___x_2057_, 4, v___x_2056_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 1);
lean_ctor_set(v___x_2049_, 0, v___x_2057_);
v___x_2059_ = v___x_2049_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2059_);
v___x_2061_ = v___x_2054_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_del_object(v___x_2049_);
lean_dec(v___x_2046_);
lean_dec(v_a_2042_);
lean_dec(v_name_2036_);
v_a_2065_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2051_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2051_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2097_; 
v_externAttrData_2074_ = lean_ctor_get(v_value_2035_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_value_2035_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2076_ = v_value_2035_;
v_isShared_2077_ = v_isSharedCheck_2097_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_externAttrData_2074_);
lean_dec(v_value_2035_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2097_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_List_isEmpty___redArg(v_externAttrData_2074_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2079_, 0, v_name_2036_);
lean_ctor_set(v___x_2079_, 1, v_a_2042_);
lean_ctor_set(v___x_2079_, 2, v___x_2046_);
lean_ctor_set(v___x_2079_, 3, v_externAttrData_2074_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2079_);
v___x_2081_ = v___x_2076_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2081_);
v___x_2083_ = v___x_2044_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
lean_del_object(v___x_2076_);
lean_dec(v_externAttrData_2074_);
lean_del_object(v___x_2044_);
v___x_2086_ = l_Lean_IR_mkDummyExternDecl(v_name_2036_, v_a_2042_, v___x_2046_);
v___x_2087_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_2086_, v_a_2032_);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2096_);
v___x_2089_ = v___x_2087_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v___x_2087_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_type_2037_);
lean_dec(v_name_2036_);
lean_dec_ref(v_value_2035_);
v_a_2099_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2041_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2041_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_IR_ToIR_lowerDecl(v_d_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_2113_, size_t v_sz_2114_, size_t v_i_2115_, lean_object* v_b_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_usize_dec_lt(v_i_2115_, v_sz_2114_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_b_2116_);
return v___x_2121_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2122_ = lean_array_uget_borrowed(v_as_2113_, v_i_2115_);
lean_inc(v_a_2122_);
v___x_2123_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_2123_, 0, v_a_2122_);
v___x_2124_ = l_Lean_IR_ToIR_M_run___redArg(v___x_2123_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v_a_2127_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
if (lean_obj_tag(v_a_2125_) == 1)
{
lean_object* v_val_2131_; lean_object* v___x_2132_; 
v_val_2131_ = lean_ctor_get(v_a_2125_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v_a_2125_, 1);
v___x_2132_ = lean_array_push(v_b_2116_, v_val_2131_);
v_a_2127_ = v___x_2132_;
goto v___jp_2126_;
}
else
{
lean_dec(v_a_2125_);
v_a_2127_ = v_b_2116_;
goto v___jp_2126_;
}
v___jp_2126_:
{
size_t v___x_2128_; size_t v___x_2129_; 
v___x_2128_ = ((size_t)1ULL);
v___x_2129_ = lean_usize_add(v_i_2115_, v___x_2128_);
v_i_2115_ = v___x_2129_;
v_b_2116_ = v_a_2127_;
goto _start;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_b_2116_);
v_a_2133_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2124_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2124_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_2141_, lean_object* v_sz_2142_, lean_object* v_i_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
size_t v_sz_boxed_2148_; size_t v_i_boxed_2149_; lean_object* v_res_2150_; 
v_sz_boxed_2148_ = lean_unbox_usize(v_sz_2142_);
lean_dec(v_sz_2142_);
v_i_boxed_2149_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_2141_, v_sz_boxed_2148_, v_i_boxed_2149_, v_b_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_as_2141_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_irDecls_2157_; size_t v_sz_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v_irDecls_2157_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_2158_ = lean_array_size(v_decls_2153_);
v___x_2159_ = ((size_t)0ULL);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_2153_, v_sz_2158_, v___x_2159_, v_irDecls_2157_, v_a_2154_, v_a_2155_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_IR_toIR(v_decls_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_decls_2161_);
return v_res_2165_;
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
