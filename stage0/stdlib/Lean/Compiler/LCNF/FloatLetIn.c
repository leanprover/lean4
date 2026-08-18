// Lean compiler output
// Module: Lean.Compiler.LCNF.FloatLetIn
// Imports: public import Lean.Compiler.LCNF.FVarUtil public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.PhaseExt
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Compiler.LCNF.FloatLetIn.Decision.default"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Compiler.LCNF.FloatLetIn.Decision.dont"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Compiler.LCNF.FloatLetIn.Decision.unknown"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Compiler.LCNF.FloatLetIn.Decision.arm"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.FVarUtil"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Compiler.LCNF.Expr.forFVarM"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "floatLetIn"};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 137, 209, 28, 15, 13, 59, 120)}};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Size of code that was pushed into arm: "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7;
static const lean_string_object l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 143, 131, 10, 85, 239, 135, 125)}};
static const lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_floatLetIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_floatLetIn___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_floatLetIn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FloatLetIn"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 171, 136, 27, 16, 174, 255, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(216, 231, 106, 157, 93, 181, 41, 85)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 255, 211, 49, 61, 191, 211, 203)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 94, 132, 169, 165, 114, 238, 204)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 74, 180, 129, 203, 146, 149, 248)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 219, 231, 242, 61, 46, 166, 166)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 21, 84, 238, 192, 65, 21, 116)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 127, 195, 142, 61, 51, 178, 181)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 60, 156, 134, 247, 42, 74, 192)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 108, 228, 187, 216, 134, 45, 241)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 162, 173, 169, 227, 67, 216, 239)}};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 0)
{
lean_object* v_name_10_; lean_object* v___x_11_; 
v_name_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_name_10_);
lean_dec_ref_known(v_t_8_, 1);
v___x_11_ = lean_apply_1(v_k_9_, v_name_10_);
return v___x_11_;
}
else
{
lean_dec(v_t_8_);
return v_k_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim___redArg(lean_object* v_t_24_, lean_object* v_arm_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_24_, v_arm_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_arm_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_28_, v_arm_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim___redArg(lean_object* v_t_32_, lean_object* v_default_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_32_, v_default_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_default_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_36_, v_default_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim___redArg(lean_object* v_t_40_, lean_object* v_dont_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_40_, v_dont_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_dont_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_44_, v_dont_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim___redArg(lean_object* v_t_48_, lean_object* v_unknown_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_48_, v_unknown_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_unknown_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_52_, v_unknown_54_);
return v___x_55_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0(void){
_start:
{
uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; 
v___x_56_ = 1723ULL;
v___x_57_ = 0ULL;
v___x_58_ = lean_uint64_mix_hash(v___x_57_, v___x_56_);
return v___x_58_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(lean_object* v_x_59_){
_start:
{
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
lean_object* v_name_60_; uint64_t v___x_61_; 
v_name_60_ = lean_ctor_get(v_x_59_, 0);
v___x_61_ = 0ULL;
if (lean_obj_tag(v_name_60_) == 0)
{
uint64_t v___x_62_; 
v___x_62_ = lean_uint64_once(&l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0);
return v___x_62_;
}
else
{
uint64_t v_hash_63_; uint64_t v___x_64_; 
v_hash_63_ = lean_ctor_get_uint64(v_name_60_, sizeof(void*)*2);
v___x_64_ = lean_uint64_mix_hash(v___x_61_, v_hash_63_);
return v___x_64_;
}
}
case 1:
{
uint64_t v___x_65_; 
v___x_65_ = 1ULL;
return v___x_65_;
}
case 2:
{
uint64_t v___x_66_; 
v___x_66_ = 2ULL;
return v___x_66_;
}
default: 
{
uint64_t v___x_67_; 
v___x_67_ = 3ULL;
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed(lean_object* v_x_68_){
_start:
{
uint64_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_x_68_);
lean_dec(v_x_68_);
v_r_70_ = lean_box_uint64(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
switch(lean_obj_tag(v_x_73_))
{
case 0:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_name_75_; lean_object* v_name_76_; uint8_t v___x_77_; 
v_name_75_ = lean_ctor_get(v_x_73_, 0);
v_name_76_ = lean_ctor_get(v_x_74_, 0);
v___x_77_ = lean_name_eq(v_name_75_, v_name_76_);
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
case 1:
{
if (lean_obj_tag(v_x_74_) == 1)
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
case 2:
{
if (lean_obj_tag(v_x_74_) == 2)
{
uint8_t v___x_81_; 
v___x_81_ = 1;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
default: 
{
if (lean_obj_tag(v_x_74_) == 3)
{
uint8_t v___x_83_; 
v___x_83_ = 1;
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_x_85_, v_x_86_);
lean_dec(v_x_86_);
lean_dec(v_x_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(2u);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(lean_object* v_x_114_, lean_object* v_prec_115_){
_start:
{
lean_object* v___y_117_; lean_object* v___y_124_; lean_object* v___y_131_; 
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
lean_object* v_name_137_; lean_object* v___y_139_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_name_137_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_name_137_);
lean_dec_ref_known(v_x_114_, 1);
v___x_148_ = lean_unsigned_to_nat(1024u);
v___x_149_ = lean_nat_dec_le(v___x_148_, v_prec_115_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_139_ = v___x_150_;
goto v___jp_138_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_139_ = v___x_151_;
goto v___jp_138_;
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_140_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8));
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = l_Lean_Name_reprPrec(v_name_137_, v___x_141_);
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_140_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
lean_inc(v___y_139_);
v___x_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_139_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_115_);
return v___x_147_;
}
}
case 1:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_prec_115_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_117_ = v___x_154_;
goto v___jp_116_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_117_ = v___x_155_;
goto v___jp_116_;
}
}
case 2:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1024u);
v___x_157_ = lean_nat_dec_le(v___x_156_, v_prec_115_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_124_ = v___x_158_;
goto v___jp_123_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_124_ = v___x_159_;
goto v___jp_123_;
}
}
default: 
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(1024u);
v___x_161_ = lean_nat_dec_le(v___x_160_, v_prec_115_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_131_ = v___x_162_;
goto v___jp_130_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_131_ = v___x_163_;
goto v___jp_130_;
}
}
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1));
lean_inc(v___y_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v_prec_115_);
return v___x_122_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3));
lean_inc(v___y_124_);
v___x_126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_126_, 0, v___y_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = 0;
v___x_128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_127_);
v___x_129_ = l_Repr_addAppParen(v___x_128_, v_prec_115_);
return v___x_129_;
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5));
lean_inc(v___y_131_);
v___x_133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_133_, 0, v___y_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_prec_115_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed(lean_object* v_x_164_, lean_object* v_prec_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v_x_164_, v_prec_165_);
lean_dec(v_prec_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_ctorName_170_; lean_object* v___x_171_; 
v_ctorName_170_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_ctorName_170_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_ctorName_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(1);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object* v_x_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_x_173_);
lean_dec_ref(v_x_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object* v_decl_175_, lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc(v_a_177_);
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v_decl_175_);
lean_ctor_set(v___x_183_, 1, v_a_177_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
v___x_184_ = lean_apply_6(v_x_176_, v___x_183_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, lean_box(0));
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg___boxed(lean_object* v_decl_185_, lean_object* v_x_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_185_, v_x_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* v_00_u03b1_194_, lean_object* v_decl_195_, lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_195_, v_x_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___boxed(lean_object* v_00_u03b1_204_, lean_object* v_decl_205_, lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(v_00_u03b1_204_, v_decl_205_, v_x_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object* v_x_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_box(0);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
v___x_221_ = lean_apply_6(v_x_214_, v___x_220_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, lean_box(0));
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg___boxed(lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* v_00_u03b1_229_, lean_object* v_x_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_230_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object* v_00_u03b1_238_, lean_object* v_x_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(v_00_u03b1_238_, v_x_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object* v_decl_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_type_253_; lean_object* v_value_254_; lean_object* v___x_255_; 
v_type_253_ = lean_ctor_get(v_decl_247_, 2);
lean_inc_ref(v_type_253_);
v_value_254_ = lean_ctor_get(v_decl_247_, 3);
lean_inc(v_value_254_);
lean_dec_ref(v_decl_247_);
v___x_255_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_253_, v_a_251_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_304_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_304_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_304_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_304_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
if (lean_obj_tag(v_a_256_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = 0;
if (lean_obj_tag(v_value_254_) == 2)
{
lean_object* v_struct_261_; lean_object* v___x_262_; 
lean_del_object(v___x_258_);
v_struct_261_ = lean_ctor_get(v_value_254_, 2);
lean_inc(v_struct_261_);
lean_dec_ref_known(v_value_254_, 3);
v___x_262_ = l_Lean_Compiler_LCNF_getType(v_struct_261_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_a_263_, v_a_251_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_278_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_278_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_278_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_278_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
if (lean_obj_tag(v_a_265_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_box(v___x_260_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec_ref_known(v_a_265_, 1);
v___x_273_ = 1;
v___x_274_ = lean_box(v___x_273_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_274_);
v___x_276_ = v___x_267_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_264_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_264_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_262_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_262_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_297_; 
lean_dec(v_value_254_);
v___x_295_ = lean_box(v___x_260_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_295_);
v___x_297_ = v___x_258_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec_ref_known(v_a_256_, 1);
lean_dec(v_value_254_);
v___x_299_ = 1;
v___x_300_ = lean_box(v___x_299_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_300_);
v___x_302_ = v___x_258_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_value_254_);
v_a_305_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_255_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_255_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object* v_decl_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* v_decl_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_320_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object* v_decl_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(v_decl_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object* v_m_336_, lean_object* v_query_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_zero_341_; uint8_t v_isZero_342_; 
v_zero_341_ = lean_unsigned_to_nat(0u);
v_isZero_342_ = lean_nat_dec_eq(v_x_339_, v_zero_341_);
if (v_isZero_342_ == 1)
{
lean_dec(v_x_340_);
lean_dec(v_x_339_);
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_343_; 
v___x_343_ = lean_box(2);
return v___x_343_;
}
else
{
lean_object* v_val_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_val_344_ = lean_ctor_get(v_x_338_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v_x_338_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_val_344_);
lean_dec(v_x_338_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_val_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_keyArray_352_; lean_object* v_valueArray_353_; lean_object* v___x_354_; uint8_t v_isSome_355_; 
v_keyArray_352_ = lean_ctor_get(v_m_336_, 1);
v_valueArray_353_ = lean_ctor_get(v_m_336_, 2);
v___x_354_ = lean_array_fget_borrowed(v_keyArray_352_, v_x_340_);
v_isSome_355_ = lean_noption_is_some(v___x_354_);
if (v_isSome_355_ == 0)
{
lean_dec(v_x_339_);
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_x_340_);
return v___x_356_;
}
else
{
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_x_340_);
v_val_357_ = lean_ctor_get(v_x_338_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v_x_338_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v_x_338_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_val_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_one_365_; lean_object* v_n_366_; lean_object* v___y_368_; 
v_one_365_ = lean_unsigned_to_nat(1u);
v_n_366_ = lean_nat_sub(v_x_339_, v_one_365_);
lean_dec(v_x_339_);
if (v_isSome_355_ == 0)
{
goto v___jp_374_;
}
else
{
lean_object* v___x_376_; uint8_t v_isSome_377_; 
v___x_376_ = lean_array_fget_borrowed(v_valueArray_353_, v_x_340_);
v_isSome_377_ = lean_noption_is_some(v___x_376_);
if (v_isSome_377_ == 0)
{
goto v___jp_374_;
}
else
{
lean_object* v_val_378_; uint8_t v___x_379_; 
lean_inc(v___x_354_);
v_val_378_ = lean_noption_get(v___x_354_);
v___x_379_ = l_Lean_instBEqFVarId_beq(v_val_378_, v_query_337_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
lean_dec(v_val_378_);
v___x_380_ = lean_array_get_size(v_keyArray_352_);
v___x_381_ = lean_nat_add(v_x_340_, v_one_365_);
lean_dec(v_x_340_);
v___x_382_ = lean_nat_dec_lt(v___x_381_, v___x_380_);
if (v___x_382_ == 0)
{
lean_dec(v___x_381_);
v_x_339_ = v_n_366_;
v_x_340_ = v_zero_341_;
goto _start;
}
else
{
v_x_339_ = v_n_366_;
v_x_340_ = v___x_381_;
goto _start;
}
}
else
{
lean_object* v_val_385_; lean_object* v___x_386_; 
lean_dec(v_n_366_);
lean_dec(v_x_338_);
lean_inc(v___x_376_);
v_val_385_ = lean_noption_get(v___x_376_);
v___x_386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_386_, 0, v_x_340_);
lean_ctor_set(v___x_386_, 1, v_val_378_);
lean_ctor_set(v___x_386_, 2, v_val_385_);
return v___x_386_;
}
}
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = lean_array_get_size(v_keyArray_352_);
v___x_370_ = lean_nat_add(v_x_340_, v_one_365_);
lean_dec(v_x_340_);
v___x_371_ = lean_nat_dec_lt(v___x_370_, v___x_369_);
if (v___x_371_ == 0)
{
lean_dec(v___x_370_);
v_x_338_ = v___y_368_;
v_x_339_ = v_n_366_;
v_x_340_ = v_zero_341_;
goto _start;
}
else
{
v_x_338_ = v___y_368_;
v_x_339_ = v_n_366_;
v_x_340_ = v___x_370_;
goto _start;
}
}
v___jp_374_:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_375_; 
lean_inc(v_x_340_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_x_340_);
v___y_368_ = v___x_375_;
goto v___jp_367_;
}
else
{
v___y_368_ = v_x_338_;
goto v___jp_367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg___boxed(lean_object* v_m_387_, lean_object* v_query_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_m_387_, v_query_388_, v_x_389_, v_x_390_, v_x_391_);
lean_dec(v_query_388_);
lean_dec_ref(v_m_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object* v_m_393_, lean_object* v_query_394_){
_start:
{
lean_object* v_keyArray_395_; lean_object* v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v_fold_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_keyArray_395_ = lean_ctor_get(v_m_393_, 1);
v___x_396_ = lean_array_get_size(v_keyArray_395_);
v___x_397_ = l_Lean_instHashableFVarId_hash(v_query_394_);
v___x_398_ = 32ULL;
v___x_399_ = lean_uint64_shift_right(v___x_397_, v___x_398_);
v_fold_400_ = lean_uint64_xor(v___x_397_, v___x_399_);
v___x_401_ = 16ULL;
v___x_402_ = lean_uint64_shift_right(v_fold_400_, v___x_401_);
v___x_403_ = lean_uint64_xor(v_fold_400_, v___x_402_);
v___x_404_ = lean_uint64_to_usize(v___x_403_);
v___x_405_ = lean_usize_of_nat(v___x_396_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_sub(v___x_405_, v___x_406_);
v___x_408_ = lean_usize_land(v___x_404_, v___x_407_);
v___x_409_ = lean_usize_to_nat(v___x_408_);
v___x_410_ = lean_box(0);
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_m_393_, v_query_394_, v___x_410_, v___x_396_, v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg___boxed(lean_object* v_m_412_, lean_object* v_query_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_412_, v_query_413_);
lean_dec(v_query_413_);
lean_dec_ref(v_m_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object* v_m_415_, lean_object* v_query_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_415_, v_query_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_index_418_; lean_object* v_key_419_; lean_object* v_value_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_index_418_ = lean_ctor_get(v___x_417_, 0);
v_key_419_ = lean_ctor_get(v___x_417_, 1);
v_value_420_ = lean_ctor_get(v___x_417_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_417_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_value_420_);
lean_inc(v_key_419_);
lean_inc(v_index_418_);
lean_dec(v___x_417_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_index_418_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_key_419_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_value_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v___x_428_; 
lean_dec(v___x_417_);
v___x_428_ = lean_box(1);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object* v_m_429_, lean_object* v_query_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_m_429_, v_query_430_);
lean_dec(v_query_430_);
lean_dec_ref(v_m_429_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object* v_m_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_m_432_, v_a_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
uint8_t v___x_435_; 
lean_dec_ref_known(v___x_434_, 3);
v___x_435_ = 1;
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object* v_m_437_, lean_object* v_a_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_m_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg(lean_object* v_b_441_, lean_object* v_acc_442_, lean_object* v_i_443_){
_start:
{
lean_object* v___y_445_; lean_object* v_keyArray_453_; lean_object* v_valueArray_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_keyArray_453_ = lean_ctor_get(v_b_441_, 1);
v_valueArray_454_ = lean_ctor_get(v_b_441_, 2);
v___x_455_ = lean_array_get_size(v_keyArray_453_);
v___x_456_ = lean_nat_dec_lt(v_i_443_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec(v_i_443_);
return v_acc_442_;
}
else
{
lean_object* v___x_457_; uint8_t v_isSome_458_; 
v___x_457_ = lean_array_fget_borrowed(v_keyArray_453_, v_i_443_);
v_isSome_458_ = lean_noption_is_some(v___x_457_);
if (v_isSome_458_ == 0)
{
goto v___jp_449_;
}
else
{
lean_object* v___x_459_; uint8_t v_isSome_460_; 
v___x_459_ = lean_array_fget_borrowed(v_valueArray_454_, v_i_443_);
v_isSome_460_ = lean_noption_is_some(v___x_459_);
if (v_isSome_460_ == 0)
{
goto v___jp_449_;
}
else
{
lean_object* v_val_461_; lean_object* v_val_462_; lean_object* v_i_464_; lean_object* v___x_469_; 
lean_inc(v___x_457_);
v_val_461_ = lean_noption_get(v___x_457_);
lean_inc(v___x_459_);
v_val_462_ = lean_noption_get(v___x_459_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_acc_442_, v_val_461_);
switch(lean_obj_tag(v___x_469_))
{
case 0:
{
lean_object* v_index_470_; lean_object* v_size_471_; lean_object* v___x_472_; 
v_index_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_index_470_);
lean_dec_ref_known(v___x_469_, 3);
v_size_471_ = lean_ctor_get(v_acc_442_, 0);
lean_inc(v_size_471_);
v___x_472_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_442_, v_size_471_, v_index_470_, v_val_461_, v_val_462_);
lean_dec(v_index_470_);
v___y_445_ = v___x_472_;
goto v___jp_444_;
}
case 1:
{
lean_object* v_index_473_; 
v_index_473_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_index_473_);
lean_dec_ref_known(v___x_469_, 1);
v_i_464_ = v_index_473_;
goto v___jp_463_;
}
default: 
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_442_, v___x_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_index_476_; 
v_index_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_index_476_);
lean_dec_ref_known(v___x_475_, 1);
v_i_464_ = v_index_476_;
goto v___jp_463_;
}
else
{
lean_dec(v_val_462_);
lean_dec(v_val_461_);
v___y_445_ = v_acc_442_;
goto v___jp_444_;
}
}
}
v___jp_463_:
{
lean_object* v_size_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_size_465_ = lean_ctor_get(v_acc_442_, 0);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_size_465_, v___x_466_);
v___x_468_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_442_, v___x_467_, v_i_464_, v_val_461_, v_val_462_);
lean_dec(v_i_464_);
v___y_445_ = v___x_468_;
goto v___jp_444_;
}
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_i_443_, v___x_446_);
lean_dec(v_i_443_);
v_acc_442_ = v___y_445_;
v_i_443_ = v___x_447_;
goto _start;
}
v___jp_449_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_add(v_i_443_, v___x_450_);
lean_dec(v_i_443_);
v_i_443_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_477_, lean_object* v_acc_478_, lean_object* v_i_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg(v_b_477_, v_acc_478_, v_i_479_);
lean_dec_ref(v_b_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg(lean_object* v_init_481_, lean_object* v_b_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg(v_b_482_, v_init_481_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg___boxed(lean_object* v_init_485_, lean_object* v_b_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg(v_init_485_, v_b_486_);
lean_dec_ref(v_b_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(lean_object* v_m_488_){
_start:
{
lean_object* v_keyArray_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_cellCount_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_target_496_; lean_object* v___x_497_; 
v_keyArray_489_ = lean_ctor_get(v_m_488_, 1);
v___x_490_ = lean_array_get_size(v_keyArray_489_);
v___x_491_ = lean_unsigned_to_nat(2u);
v_cellCount_492_ = lean_nat_mul(v___x_490_, v___x_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_492_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_492_);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_492_);
v_target_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_496_, 0, v___x_493_);
lean_ctor_set(v_target_496_, 1, v___x_494_);
lean_ctor_set(v_target_496_, 2, v___x_495_);
v___x_497_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg(v_target_496_, v_m_488_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg___boxed(lean_object* v_m_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_m_498_);
lean_dec_ref(v_m_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object* v_var_500_, uint8_t v_borrowed_501_, lean_object* v_a_502_){
_start:
{
if (lean_obj_tag(v_var_500_) == 1)
{
lean_object* v_fvarId_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_584_; 
v_fvarId_504_ = lean_ctor_get(v_var_500_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_var_500_);
if (v_isSharedCheck_584_ == 0)
{
v___x_506_ = v_var_500_;
v_isShared_507_ = v_isSharedCheck_584_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_fvarId_504_);
lean_dec(v_var_500_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_584_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_st_ref_get(v_a_502_);
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_508_, v_fvarId_504_);
lean_dec(v___x_508_);
if (v_borrowed_501_ == 0)
{
lean_object* v___x_510_; lean_object* v___y_512_; lean_object* v___x_518_; lean_object* v___y_520_; lean_object* v_i_521_; lean_object* v___y_527_; lean_object* v___y_537_; lean_object* v_i_538_; lean_object* v___x_553_; 
v___x_510_ = lean_st_ref_take(v_a_502_);
v___x_518_ = lean_box(0);
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_510_, v_fvarId_504_);
switch(lean_obj_tag(v___x_553_))
{
case 0:
{
lean_dec_ref_known(v___x_553_, 3);
lean_dec(v_fvarId_504_);
v___y_512_ = v___x_510_;
goto v___jp_511_;
}
case 1:
{
lean_object* v_index_554_; lean_object* v_size_555_; lean_object* v_keyArray_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_index_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_index_554_);
lean_dec_ref_known(v___x_553_, 1);
v_size_555_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_size_555_);
v_keyArray_556_ = lean_ctor_get(v___x_510_, 1);
lean_inc_ref(v_keyArray_556_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_size_555_, v___x_557_);
lean_dec(v_size_555_);
v___x_559_ = lean_array_get_size(v_keyArray_556_);
lean_dec_ref(v_keyArray_556_);
v___x_560_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v___x_558_);
lean_dec(v_index_554_);
goto v___jp_543_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_561_ = lean_unsigned_to_nat(4u);
v___x_562_ = lean_nat_mul(v___x_558_, v___x_561_);
v___x_563_ = lean_unsigned_to_nat(3u);
v___x_564_ = lean_nat_mul(v___x_559_, v___x_563_);
v___x_565_ = lean_nat_dec_le(v___x_562_, v___x_564_);
lean_dec(v___x_564_);
lean_dec(v___x_562_);
if (v___x_565_ == 0)
{
lean_dec(v___x_558_);
lean_dec(v_index_554_);
goto v___jp_543_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_510_, v___x_558_, v_index_554_, v_fvarId_504_, v___x_518_);
lean_dec(v_index_554_);
v___y_512_ = v___x_566_;
goto v___jp_511_;
}
}
}
default: 
{
lean_object* v_size_567_; lean_object* v_keyArray_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_size_567_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_size_567_);
v_keyArray_568_ = lean_ctor_get(v___x_510_, 1);
lean_inc_ref(v_keyArray_568_);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_size_567_, v___x_569_);
lean_dec(v_size_567_);
v___x_571_ = lean_array_get_size(v_keyArray_568_);
lean_dec_ref(v_keyArray_568_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v___x_570_);
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_510_);
lean_dec(v___x_510_);
v___y_527_ = v___x_573_;
goto v___jp_526_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_574_ = lean_unsigned_to_nat(4u);
v___x_575_ = lean_nat_mul(v___x_570_, v___x_574_);
lean_dec(v___x_570_);
v___x_576_ = lean_unsigned_to_nat(3u);
v___x_577_ = lean_nat_mul(v___x_571_, v___x_576_);
v___x_578_ = lean_nat_dec_le(v___x_575_, v___x_577_);
lean_dec(v___x_577_);
lean_dec(v___x_575_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_510_);
lean_dec(v___x_510_);
v___y_527_ = v___x_579_;
goto v___jp_526_;
}
else
{
v___y_527_ = v___x_510_;
goto v___jp_526_;
}
}
}
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = lean_st_ref_put(v_a_502_, v___y_512_);
v___x_514_ = lean_box(v___x_509_);
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 0);
lean_ctor_set(v___x_506_, 0, v___x_514_);
v___x_516_ = v___x_506_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
v___jp_519_:
{
lean_object* v_size_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_size_522_ = lean_ctor_get(v___y_520_, 0);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_size_522_, v___x_523_);
v___x_525_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_520_, v___x_524_, v_i_521_, v_fvarId_504_, v___x_518_);
lean_dec(v_i_521_);
v___y_512_ = v___x_525_;
goto v___jp_511_;
}
v___jp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_527_, v_fvarId_504_);
switch(lean_obj_tag(v___x_528_))
{
case 0:
{
lean_object* v_index_529_; lean_object* v_size_530_; lean_object* v___x_531_; 
v_index_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_index_529_);
lean_dec_ref_known(v___x_528_, 3);
v_size_530_ = lean_ctor_get(v___y_527_, 0);
lean_inc(v_size_530_);
v___x_531_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_527_, v_size_530_, v_index_529_, v_fvarId_504_, v___x_518_);
lean_dec(v_index_529_);
v___y_512_ = v___x_531_;
goto v___jp_511_;
}
case 1:
{
lean_object* v_index_532_; 
v_index_532_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_index_532_);
lean_dec_ref_known(v___x_528_, 1);
v___y_520_ = v___y_527_;
v_i_521_ = v_index_532_;
goto v___jp_519_;
}
default: 
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_527_, v___x_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_index_535_; 
v_index_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_index_535_);
lean_dec_ref_known(v___x_534_, 1);
v___y_520_ = v___y_527_;
v_i_521_ = v_index_535_;
goto v___jp_519_;
}
else
{
lean_dec(v_fvarId_504_);
v___y_512_ = v___y_527_;
goto v___jp_511_;
}
}
}
}
v___jp_536_:
{
lean_object* v_size_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_size_539_ = lean_ctor_get(v___y_537_, 0);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_size_539_, v___x_540_);
v___x_542_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_537_, v___x_541_, v_i_538_, v_fvarId_504_, v___x_518_);
lean_dec(v_i_538_);
v___y_512_ = v___x_542_;
goto v___jp_511_;
}
v___jp_543_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_510_);
lean_dec(v___x_510_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_544_, v_fvarId_504_);
switch(lean_obj_tag(v___x_545_))
{
case 0:
{
lean_object* v_index_546_; lean_object* v_size_547_; lean_object* v___x_548_; 
v_index_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_545_, 3);
v_size_547_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_size_547_);
v___x_548_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_544_, v_size_547_, v_index_546_, v_fvarId_504_, v___x_518_);
lean_dec(v_index_546_);
v___y_512_ = v___x_548_;
goto v___jp_511_;
}
case 1:
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_545_, 1);
v___y_537_ = v___x_544_;
v_i_538_ = v_index_549_;
goto v___jp_536_;
}
default: 
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_544_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_index_552_; 
v_index_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_index_552_);
lean_dec_ref_known(v___x_551_, 1);
v___y_537_ = v___x_544_;
v_i_538_ = v_index_552_;
goto v___jp_536_;
}
else
{
lean_dec(v_fvarId_504_);
v___y_512_ = v___x_544_;
goto v___jp_511_;
}
}
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_fvarId_504_);
v___x_580_ = lean_box(v___x_509_);
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 0);
lean_ctor_set(v___x_506_, 0, v___x_580_);
v___x_582_ = v___x_506_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_var_500_);
v___x_585_ = 0;
v___x_586_ = lean_box(v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object* v_var_588_, lean_object* v_borrowed_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
uint8_t v_borrowed_boxed_592_; lean_object* v_res_593_; 
v_borrowed_boxed_592_ = lean_unbox(v_borrowed_589_);
v_res_593_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_588_, v_borrowed_boxed_592_, v_a_590_);
lean_dec(v_a_590_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object* v_var_594_, uint8_t v_borrowed_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_594_, v_borrowed_595_, v_a_596_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object* v_var_603_, lean_object* v_borrowed_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
uint8_t v_borrowed_boxed_611_; lean_object* v_res_612_; 
v_borrowed_boxed_611_ = lean_unbox(v_borrowed_604_);
v_res_612_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_603_, v_borrowed_boxed_611_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
return v_res_612_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object* v_00_u03b2_613_, lean_object* v_m_614_, lean_object* v_a_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_614_, v_a_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object* v_00_u03b2_617_, lean_object* v_m_618_, lean_object* v_a_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_617_, v_m_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_m_618_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object* v_00_u03b2_622_, lean_object* v_m_623_, lean_object* v_query_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_623_, v_query_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___boxed(lean_object* v_00_u03b2_626_, lean_object* v_m_627_, lean_object* v_query_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(v_00_u03b2_626_, v_m_627_, v_query_628_);
lean_dec(v_query_628_);
lean_dec_ref(v_m_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2(lean_object* v_00_u03b2_630_, lean_object* v_m_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_m_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___boxed(lean_object* v_00_u03b2_633_, lean_object* v_m_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2(v_00_u03b2_633_, v_m_634_);
lean_dec_ref(v_m_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object* v_00_u03b2_636_, lean_object* v_m_637_, lean_object* v_query_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_m_637_, v_query_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_640_, lean_object* v_m_641_, lean_object* v_query_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_640_, v_m_641_, v_query_642_);
lean_dec(v_query_642_);
lean_dec_ref(v_m_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object* v_00_u03b2_644_, lean_object* v_m_645_, lean_object* v_query_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_m_645_, v_query_646_, v_x_647_, v_x_648_, v_x_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___boxed(lean_object* v_00_u03b2_652_, lean_object* v_m_653_, lean_object* v_query_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(v_00_u03b2_652_, v_m_653_, v_query_654_, v_x_655_, v_x_656_, v_x_657_, v_x_658_);
lean_dec(v_query_654_);
lean_dec_ref(v_m_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4(lean_object* v_00_u03b2_660_, lean_object* v_init_661_, lean_object* v_b_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___redArg(v_init_661_, v_b_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4___boxed(lean_object* v_00_u03b2_664_, lean_object* v_init_665_, lean_object* v_b_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4(v_00_u03b2_664_, v_init_665_, v_b_666_);
lean_dec_ref(v_b_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_668_, lean_object* v_b_669_, lean_object* v_acc_670_, lean_object* v_i_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___redArg(v_b_669_, v_acc_670_, v_i_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_673_, lean_object* v_b_674_, lean_object* v_acc_675_, lean_object* v_i_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2_spec__4_spec__5(v_00_u03b2_673_, v_b_674_, v_acc_675_, v_i_676_);
lean_dec_ref(v_b_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_678_, lean_object* v_args_679_, lean_object* v_val_680_, lean_object* v_a_681_, uint8_t v_b_682_, lean_object* v___y_683_){
_start:
{
uint8_t v_a_686_; uint8_t v___x_690_; 
v___x_690_ = lean_nat_dec_lt(v_a_681_, v_upperBound_678_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_a_681_);
v___x_691_ = lean_box(v_b_682_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v_params_693_; lean_object* v___x_694_; uint8_t v___y_696_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_params_693_ = lean_ctor_get(v_val_680_, 3);
v___x_694_ = lean_array_fget_borrowed(v_args_679_, v_a_681_);
v___x_701_ = lean_array_get_size(v_params_693_);
v___x_702_ = lean_nat_dec_lt(v_a_681_, v___x_701_);
if (v___x_702_ == 0)
{
v___y_696_ = v___x_702_;
goto v___jp_695_;
}
else
{
lean_object* v___x_703_; uint8_t v_borrow_704_; 
v___x_703_ = lean_array_fget_borrowed(v_params_693_, v_a_681_);
v_borrow_704_ = lean_ctor_get_uint8(v___x_703_, sizeof(void*)*3);
v___y_696_ = v_borrow_704_;
goto v___jp_695_;
}
v___jp_695_:
{
lean_object* v___x_697_; 
lean_inc(v___x_694_);
v___x_697_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_694_, v___y_696_, v___y_683_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; uint8_t v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = lean_unbox(v_a_698_);
if (v___x_699_ == 0)
{
lean_dec(v_a_698_);
v_a_686_ = v_b_682_;
goto v___jp_685_;
}
else
{
uint8_t v___x_700_; 
v___x_700_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
v_a_686_ = v___x_700_;
goto v___jp_685_;
}
}
else
{
lean_dec(v_a_681_);
return v___x_697_;
}
}
}
v___jp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_add(v_a_681_, v___x_687_);
lean_dec(v_a_681_);
v_a_681_ = v___x_688_;
v_b_682_ = v_a_686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object* v_upperBound_705_, lean_object* v_args_706_, lean_object* v_val_707_, lean_object* v_a_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v_b_boxed_712_; lean_object* v_res_713_; 
v_b_boxed_712_ = lean_unbox(v_b_709_);
v_res_713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_705_, v_args_706_, v_val_707_, v_a_708_, v_b_boxed_712_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v_val_707_);
lean_dec_ref(v_args_706_);
lean_dec(v_upperBound_705_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object* v_as_714_, size_t v_i_715_, size_t v_stop_716_, uint8_t v_b_717_, lean_object* v___y_718_){
_start:
{
uint8_t v_a_721_; lean_object* v___y_726_; uint8_t v___x_729_; 
v___x_729_ = lean_usize_dec_eq(v_i_715_, v_stop_716_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_array_uget_borrowed(v_as_714_, v_i_715_);
lean_inc(v___x_730_);
v___x_731_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_730_, v___x_729_, v___y_718_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; uint8_t v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
v___x_733_ = lean_unbox(v_a_732_);
lean_dec(v_a_732_);
if (v___x_733_ == 0)
{
lean_dec_ref_known(v___x_731_, 1);
v_a_721_ = v_b_717_;
goto v___jp_720_;
}
else
{
v___y_726_ = v___x_731_;
goto v___jp_725_;
}
}
else
{
v___y_726_ = v___x_731_;
goto v___jp_725_;
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(v_b_717_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
v___jp_720_:
{
size_t v___x_722_; size_t v___x_723_; 
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_715_, v___x_722_);
v_i_715_ = v___x_723_;
v_b_717_ = v_a_721_;
goto _start;
}
v___jp_725_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
lean_object* v_a_727_; uint8_t v___x_728_; 
v_a_727_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___y_726_, 1);
v___x_728_ = lean_unbox(v_a_727_);
lean_dec(v_a_727_);
v_a_721_ = v___x_728_;
goto v___jp_720_;
}
else
{
return v___y_726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_736_, lean_object* v_i_737_, lean_object* v_stop_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
size_t v_i_boxed_742_; size_t v_stop_boxed_743_; uint8_t v_b_boxed_744_; lean_object* v_res_745_; 
v_i_boxed_742_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_stop_boxed_743_ = lean_unbox_usize(v_stop_738_);
lean_dec(v_stop_738_);
v_b_boxed_744_ = lean_unbox(v_b_739_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_736_, v_i_boxed_742_, v_stop_boxed_743_, v_b_boxed_744_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v_as_736_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object* v_as_746_, size_t v_i_747_, size_t v_stop_748_, uint8_t v_b_749_, lean_object* v___y_750_){
_start:
{
uint8_t v_a_753_; lean_object* v___y_758_; uint8_t v___x_761_; 
v___x_761_ = lean_usize_dec_eq(v_i_747_, v_stop_748_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_array_uget_borrowed(v_as_746_, v_i_747_);
lean_inc(v___x_762_);
v___x_763_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_762_, v___x_761_, v___y_750_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; uint8_t v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
v___x_765_ = lean_unbox(v_a_764_);
lean_dec(v_a_764_);
if (v___x_765_ == 0)
{
lean_dec_ref_known(v___x_763_, 1);
v_a_753_ = v_b_749_;
goto v___jp_752_;
}
else
{
v___y_758_ = v___x_763_;
goto v___jp_757_;
}
}
else
{
v___y_758_ = v___x_763_;
goto v___jp_757_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_box(v_b_749_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
v___jp_752_:
{
size_t v___x_754_; size_t v___x_755_; 
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_747_, v___x_754_);
v_i_747_ = v___x_755_;
v_b_749_ = v_a_753_;
goto _start;
}
v___jp_757_:
{
if (lean_obj_tag(v___y_758_) == 0)
{
lean_object* v_a_759_; uint8_t v___x_760_; 
v_a_759_ = lean_ctor_get(v___y_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___y_758_, 1);
v___x_760_ = lean_unbox(v_a_759_);
lean_dec(v_a_759_);
v_a_753_ = v___x_760_;
goto v___jp_752_;
}
else
{
return v___y_758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_768_, lean_object* v_i_769_, lean_object* v_stop_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
size_t v_i_boxed_774_; size_t v_stop_boxed_775_; uint8_t v_b_boxed_776_; lean_object* v_res_777_; 
v_i_boxed_774_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_stop_boxed_775_ = lean_unbox_usize(v_stop_770_);
lean_dec(v_stop_770_);
v_b_boxed_776_ = lean_unbox(v_b_771_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_768_, v_i_boxed_774_, v_stop_boxed_775_, v_b_boxed_776_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v_as_768_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object* v_value_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
switch(lean_obj_tag(v_value_778_))
{
case 0:
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v_isSharedCheck_793_ = !lean_is_exclusive(v_value_778_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_value_778_, 0);
lean_dec(v_unused_794_);
v___x_786_ = v_value_778_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_value_778_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = 0;
v___x_789_ = lean_box(v___x_788_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
case 1:
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = 0;
v___x_796_ = lean_box(v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
case 2:
{
lean_object* v_struct_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; 
v_struct_798_ = lean_ctor_get(v_value_778_, 2);
lean_inc(v_struct_798_);
lean_dec_ref_known(v_value_778_, 3);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v_struct_798_);
v___x_800_ = 1;
v___x_801_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_799_, v___x_800_, v_a_779_);
return v___x_801_;
}
case 3:
{
lean_object* v_declName_802_; lean_object* v_args_803_; lean_object* v___x_804_; 
v_declName_802_ = lean_ctor_get(v_value_778_, 0);
lean_inc(v_declName_802_);
v_args_803_ = lean_ctor_get(v_value_778_, 2);
lean_inc_ref(v_args_803_);
lean_dec_ref_known(v_value_778_, 3);
v___x_804_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_802_, v_a_783_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_833_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_833_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_833_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_833_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
if (lean_obj_tag(v_a_805_) == 0)
{
uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_809_ = 0;
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v_args_803_);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec_ref(v_args_803_);
v___x_813_ = lean_box(v___x_809_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_813_);
v___x_815_ = v___x_807_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_le(v___x_811_, v___x_811_);
if (v___x_817_ == 0)
{
if (v___x_812_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_820_; 
lean_dec_ref(v_args_803_);
v___x_818_ = lean_box(v___x_809_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_818_);
v___x_820_ = v___x_807_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
lean_del_object(v___x_807_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_811_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_803_, v___x_822_, v___x_823_, v___x_809_, v_a_779_);
lean_dec_ref(v_args_803_);
return v___x_824_;
}
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_807_);
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_811_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_803_, v___x_825_, v___x_826_, v___x_809_, v_a_779_);
lean_dec_ref(v_args_803_);
return v___x_827_;
}
}
}
else
{
lean_object* v_val_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_807_);
v_val_828_ = lean_ctor_get(v_a_805_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v_a_805_, 1);
v___x_829_ = lean_array_get_size(v_args_803_);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = 0;
v___x_832_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_829_, v_args_803_, v_val_828_, v___x_830_, v___x_831_, v_a_779_);
lean_dec(v_val_828_);
lean_dec_ref(v_args_803_);
return v___x_832_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v_args_803_);
v_a_834_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_804_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_804_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
default: 
{
lean_object* v_fvarId_842_; lean_object* v_args_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_fvarId_842_ = lean_ctor_get(v_value_778_, 0);
lean_inc(v_fvarId_842_);
v_args_843_ = lean_ctor_get(v_value_778_, 1);
lean_inc_ref(v_args_843_);
lean_dec_ref_known(v_value_778_, 2);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_fvarId_842_);
v___x_845_ = 0;
v___x_846_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_844_, v___x_845_, v_a_779_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get_size(v_args_843_);
v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec(v_a_847_);
lean_dec_ref(v_args_843_);
return v___x_846_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = lean_nat_dec_le(v___x_849_, v___x_849_);
if (v___x_851_ == 0)
{
if (v___x_850_ == 0)
{
lean_dec(v_a_847_);
lean_dec_ref(v_args_843_);
return v___x_846_;
}
else
{
size_t v___x_852_; size_t v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; 
lean_dec_ref(v___x_846_);
v___x_852_ = ((size_t)0ULL);
v___x_853_ = lean_usize_of_nat(v___x_849_);
v___x_854_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_843_, v___x_852_, v___x_853_, v___x_854_, v_a_779_);
lean_dec_ref(v_args_843_);
return v___x_855_;
}
}
else
{
size_t v___x_856_; size_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v___x_846_);
v___x_856_ = ((size_t)0ULL);
v___x_857_ = lean_usize_of_nat(v___x_849_);
v___x_858_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_843_, v___x_856_, v___x_857_, v___x_858_, v_a_779_);
lean_dec_ref(v_args_843_);
return v___x_859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(lean_object* v_value_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object* v_env_868_, lean_object* v_value_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object* v_env_877_, lean_object* v_value_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_877_, v_value_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_env_877_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object* v_as_886_, size_t v_i_887_, size_t v_stop_888_, uint8_t v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_886_, v_i_887_, v_stop_888_, v_b_889_, v___y_890_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object* v_as_897_, lean_object* v_i_898_, lean_object* v_stop_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
size_t v_i_boxed_907_; size_t v_stop_boxed_908_; uint8_t v_b_boxed_909_; lean_object* v_res_910_; 
v_i_boxed_907_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_stop_boxed_908_ = lean_unbox_usize(v_stop_899_);
lean_dec(v_stop_899_);
v_b_boxed_909_ = lean_unbox(v_b_900_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_897_, v_i_boxed_907_, v_stop_boxed_908_, v_b_boxed_909_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v_as_897_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object* v_upperBound_911_, lean_object* v_args_912_, lean_object* v_val_913_, lean_object* v_inst_914_, lean_object* v_R_915_, lean_object* v_a_916_, uint8_t v_b_917_, lean_object* v_c_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_911_, v_args_912_, v_val_913_, v_a_916_, v_b_917_, v___y_919_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object* v_upperBound_926_, lean_object* v_args_927_, lean_object* v_val_928_, lean_object* v_inst_929_, lean_object* v_R_930_, lean_object* v_a_931_, lean_object* v_b_932_, lean_object* v_c_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v_b_boxed_940_; lean_object* v_res_941_; 
v_b_boxed_940_ = lean_unbox(v_b_932_);
v_res_941_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_926_, v_args_927_, v_val_928_, v_inst_929_, v_R_930_, v_a_931_, v_b_boxed_940_, v_c_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v_val_928_);
lean_dec_ref(v_args_927_);
lean_dec(v_upperBound_926_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object* v_as_942_, size_t v_i_943_, size_t v_stop_944_, uint8_t v_b_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_942_, v_i_943_, v_stop_944_, v_b_945_, v___y_946_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object* v_as_953_, lean_object* v_i_954_, lean_object* v_stop_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
size_t v_i_boxed_963_; size_t v_stop_boxed_964_; uint8_t v_b_boxed_965_; lean_object* v_res_966_; 
v_i_boxed_963_ = lean_unbox_usize(v_i_954_);
lean_dec(v_i_954_);
v_stop_boxed_964_ = lean_unbox_usize(v_stop_955_);
lean_dec(v_stop_955_);
v_b_boxed_965_ = lean_unbox(v_b_956_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_953_, v_i_boxed_963_, v_stop_boxed_964_, v_b_boxed_965_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v_as_953_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object* v_value_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
if (lean_obj_tag(v_value_967_) == 0)
{
lean_object* v_decl_974_; lean_object* v_value_975_; lean_object* v___x_976_; 
v_decl_974_ = lean_ctor_get(v_value_967_, 0);
lean_inc_ref(v_decl_974_);
lean_dec_ref_known(v_value_967_, 1);
v_value_975_ = lean_ctor_get(v_decl_974_, 3);
lean_inc(v_value_975_);
lean_dec_ref(v_decl_974_);
v___x_976_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_975_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_976_;
}
else
{
uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec_ref(v_value_967_);
v___x_977_ = 0;
v___x_978_ = lean_box(v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object* v_value_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object* v_env_988_, lean_object* v_value_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object* v_env_997_, lean_object* v_value_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_997_, v_value_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_env_997_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object* v_m_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_m_1006_, v_a_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_value_1009_; lean_object* v___x_1010_; 
v_value_1009_ = lean_ctor_get(v___x_1008_, 2);
lean_inc(v_value_1009_);
lean_dec_ref_known(v___x_1008_, 3);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_value_1009_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_box(0);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object* v_m_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_m_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* v_plannedDecision_1015_, lean_object* v_var_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_st_ref_get(v_a_1017_);
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_1019_, v_var_1016_);
lean_dec(v___x_1019_);
if (lean_obj_tag(v___x_1020_) == 1)
{
lean_object* v_val_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1175_; 
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1175_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_val_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1175_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
if (lean_obj_tag(v_val_1021_) == 3)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___y_1028_; lean_object* v___y_1034_; lean_object* v_i_1035_; lean_object* v___y_1051_; lean_object* v_i_1052_; lean_object* v___y_1058_; lean_object* v___x_1067_; 
v___x_1025_ = lean_st_ref_take(v_a_1017_);
v___x_1026_ = lean_box(0);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_1025_, v_var_1016_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; 
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1025_, v_size_1069_, v_index_1068_, v_var_1016_, v_plannedDecision_1015_);
lean_dec(v_index_1068_);
v___y_1028_ = v___x_1070_;
goto v___jp_1027_;
}
case 1:
{
lean_object* v_index_1071_; lean_object* v_size_1072_; lean_object* v_keyArray_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_index_1071_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1071_);
lean_dec_ref_known(v___x_1067_, 1);
v_size_1072_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_size_1072_);
v_keyArray_1073_ = lean_ctor_get(v___x_1025_, 1);
lean_inc_ref(v_keyArray_1073_);
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_nat_add(v_size_1072_, v___x_1074_);
lean_dec(v_size_1072_);
v___x_1076_ = lean_array_get_size(v_keyArray_1073_);
lean_dec_ref(v_keyArray_1073_);
v___x_1077_ = lean_nat_dec_lt(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec(v___x_1075_);
lean_dec(v_index_1071_);
goto v___jp_1040_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1078_ = lean_unsigned_to_nat(4u);
v___x_1079_ = lean_nat_mul(v___x_1075_, v___x_1078_);
v___x_1080_ = lean_unsigned_to_nat(3u);
v___x_1081_ = lean_nat_mul(v___x_1076_, v___x_1080_);
v___x_1082_ = lean_nat_dec_le(v___x_1079_, v___x_1081_);
lean_dec(v___x_1081_);
lean_dec(v___x_1079_);
if (v___x_1082_ == 0)
{
lean_dec(v___x_1075_);
lean_dec(v_index_1071_);
goto v___jp_1040_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1025_, v___x_1075_, v_index_1071_, v_var_1016_, v_plannedDecision_1015_);
lean_dec(v_index_1071_);
v___y_1028_ = v___x_1083_;
goto v___jp_1027_;
}
}
}
default: 
{
lean_object* v_size_1084_; lean_object* v_keyArray_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_size_1084_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_size_1084_);
v_keyArray_1085_ = lean_ctor_get(v___x_1025_, 1);
lean_inc_ref(v_keyArray_1085_);
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_size_1084_, v___x_1086_);
lean_dec(v_size_1084_);
v___x_1088_ = lean_array_get_size(v_keyArray_1085_);
lean_dec_ref(v_keyArray_1085_);
v___x_1089_ = lean_nat_dec_lt(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v___x_1087_);
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_1025_);
lean_dec(v___x_1025_);
v___y_1058_ = v___x_1090_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1091_ = lean_unsigned_to_nat(4u);
v___x_1092_ = lean_nat_mul(v___x_1087_, v___x_1091_);
lean_dec(v___x_1087_);
v___x_1093_ = lean_unsigned_to_nat(3u);
v___x_1094_ = lean_nat_mul(v___x_1088_, v___x_1093_);
v___x_1095_ = lean_nat_dec_le(v___x_1092_, v___x_1094_);
lean_dec(v___x_1094_);
lean_dec(v___x_1092_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_1025_);
lean_dec(v___x_1025_);
v___y_1058_ = v___x_1096_;
goto v___jp_1057_;
}
else
{
v___y_1058_ = v___x_1025_;
goto v___jp_1057_;
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_st_ref_put(v_a_1017_, v___y_1028_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1026_);
v___x_1031_ = v___x_1023_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
v___jp_1033_:
{
lean_object* v_size_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_size_1036_ = lean_ctor_get(v___y_1034_, 0);
v___x_1037_ = lean_unsigned_to_nat(1u);
v___x_1038_ = lean_nat_add(v_size_1036_, v___x_1037_);
v___x_1039_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1034_, v___x_1038_, v_i_1035_, v_var_1016_, v_plannedDecision_1015_);
lean_dec(v_i_1035_);
v___y_1028_ = v___x_1039_;
goto v___jp_1027_;
}
v___jp_1040_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_1025_);
lean_dec(v___x_1025_);
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_1041_, v_var_1016_);
switch(lean_obj_tag(v___x_1042_))
{
case 0:
{
lean_object* v_index_1043_; lean_object* v_size_1044_; lean_object* v___x_1045_; 
v_index_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_index_1043_);
lean_dec_ref_known(v___x_1042_, 3);
v_size_1044_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_size_1044_);
v___x_1045_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1041_, v_size_1044_, v_index_1043_, v_var_1016_, v_plannedDecision_1015_);
lean_dec(v_index_1043_);
v___y_1028_ = v___x_1045_;
goto v___jp_1027_;
}
case 1:
{
lean_object* v_index_1046_; 
v_index_1046_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_index_1046_);
lean_dec_ref_known(v___x_1042_, 1);
v___y_1034_ = v___x_1041_;
v_i_1035_ = v_index_1046_;
goto v___jp_1033_;
}
default: 
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1041_, v___x_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_index_1049_; 
v_index_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_index_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___y_1034_ = v___x_1041_;
v_i_1035_ = v_index_1049_;
goto v___jp_1033_;
}
else
{
lean_dec(v_var_1016_);
lean_dec(v_plannedDecision_1015_);
v___y_1028_ = v___x_1041_;
goto v___jp_1027_;
}
}
}
}
v___jp_1050_:
{
lean_object* v_size_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_size_1053_ = lean_ctor_get(v___y_1051_, 0);
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_add(v_size_1053_, v___x_1054_);
v___x_1056_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1051_, v___x_1055_, v_i_1052_, v_var_1016_, v_plannedDecision_1015_);
lean_dec(v_i_1052_);
v___y_1028_ = v___x_1056_;
goto v___jp_1027_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_1058_, v_var_1016_);
switch(lean_obj_tag(v___x_1059_))
{
case 0:
{
lean_object* v_index_1060_; lean_object* v_size_1061_; lean_object* v___x_1062_; 
v_index_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_index_1060_);
lean_dec_ref_known(v___x_1059_, 3);
v_size_1061_ = lean_ctor_get(v___y_1058_, 0);
lean_inc(v_size_1061_);
v___x_1062_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1058_, v_size_1061_, v_index_1060_, v_var_1016_, v_plannedDecision_1015_);
lean_dec(v_index_1060_);
v___y_1028_ = v___x_1062_;
goto v___jp_1027_;
}
case 1:
{
lean_object* v_index_1063_; 
v_index_1063_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_index_1063_);
lean_dec_ref_known(v___x_1059_, 1);
v___y_1051_ = v___y_1058_;
v_i_1052_ = v_index_1063_;
goto v___jp_1050_;
}
default: 
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1058_, v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_index_1066_; 
v_index_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_index_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___y_1051_ = v___y_1058_;
v_i_1052_ = v_index_1066_;
goto v___jp_1050_;
}
else
{
lean_dec(v_var_1016_);
lean_dec(v_plannedDecision_1015_);
v___y_1028_ = v___y_1058_;
goto v___jp_1027_;
}
}
}
}
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_1021_, v_plannedDecision_1015_);
lean_dec(v_plannedDecision_1015_);
lean_dec(v_val_1021_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___y_1101_; lean_object* v___x_1106_; lean_object* v___y_1108_; lean_object* v_i_1109_; lean_object* v___y_1115_; lean_object* v___y_1125_; lean_object* v_i_1126_; lean_object* v___x_1141_; 
v___x_1098_ = lean_st_ref_take(v_a_1017_);
v___x_1099_ = lean_box(0);
v___x_1106_ = lean_box(2);
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_1098_, v_var_1016_);
switch(lean_obj_tag(v___x_1141_))
{
case 0:
{
lean_object* v_index_1142_; lean_object* v_size_1143_; lean_object* v___x_1144_; 
v_index_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_index_1142_);
lean_dec_ref_known(v___x_1141_, 3);
v_size_1143_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_size_1143_);
v___x_1144_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1098_, v_size_1143_, v_index_1142_, v_var_1016_, v___x_1106_);
lean_dec(v_index_1142_);
v___y_1101_ = v___x_1144_;
goto v___jp_1100_;
}
case 1:
{
lean_object* v_index_1145_; lean_object* v_size_1146_; lean_object* v_keyArray_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_index_1145_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_index_1145_);
lean_dec_ref_known(v___x_1141_, 1);
v_size_1146_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_size_1146_);
v_keyArray_1147_ = lean_ctor_get(v___x_1098_, 1);
lean_inc_ref(v_keyArray_1147_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_size_1146_, v___x_1148_);
lean_dec(v_size_1146_);
v___x_1150_ = lean_array_get_size(v_keyArray_1147_);
lean_dec_ref(v_keyArray_1147_);
v___x_1151_ = lean_nat_dec_lt(v___x_1149_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec(v___x_1149_);
lean_dec(v_index_1145_);
goto v___jp_1131_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1152_ = lean_unsigned_to_nat(4u);
v___x_1153_ = lean_nat_mul(v___x_1149_, v___x_1152_);
v___x_1154_ = lean_unsigned_to_nat(3u);
v___x_1155_ = lean_nat_mul(v___x_1150_, v___x_1154_);
v___x_1156_ = lean_nat_dec_le(v___x_1153_, v___x_1155_);
lean_dec(v___x_1155_);
lean_dec(v___x_1153_);
if (v___x_1156_ == 0)
{
lean_dec(v___x_1149_);
lean_dec(v_index_1145_);
goto v___jp_1131_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1098_, v___x_1149_, v_index_1145_, v_var_1016_, v___x_1106_);
lean_dec(v_index_1145_);
v___y_1101_ = v___x_1157_;
goto v___jp_1100_;
}
}
}
default: 
{
lean_object* v_size_1158_; lean_object* v_keyArray_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_size_1158_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_size_1158_);
v_keyArray_1159_ = lean_ctor_get(v___x_1098_, 1);
lean_inc_ref(v_keyArray_1159_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_size_1158_, v___x_1160_);
lean_dec(v_size_1158_);
v___x_1162_ = lean_array_get_size(v_keyArray_1159_);
lean_dec_ref(v_keyArray_1159_);
v___x_1163_ = lean_nat_dec_lt(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec(v___x_1161_);
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_1098_);
lean_dec(v___x_1098_);
v___y_1115_ = v___x_1164_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1165_ = lean_unsigned_to_nat(4u);
v___x_1166_ = lean_nat_mul(v___x_1161_, v___x_1165_);
lean_dec(v___x_1161_);
v___x_1167_ = lean_unsigned_to_nat(3u);
v___x_1168_ = lean_nat_mul(v___x_1162_, v___x_1167_);
v___x_1169_ = lean_nat_dec_le(v___x_1166_, v___x_1168_);
lean_dec(v___x_1168_);
lean_dec(v___x_1166_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_1098_);
lean_dec(v___x_1098_);
v___y_1115_ = v___x_1170_;
goto v___jp_1114_;
}
else
{
v___y_1115_ = v___x_1098_;
goto v___jp_1114_;
}
}
}
}
v___jp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_st_ref_put(v_a_1017_, v___y_1101_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1099_);
v___x_1104_ = v___x_1023_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
v___jp_1107_:
{
lean_object* v_size_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_size_1110_ = lean_ctor_get(v___y_1108_, 0);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_size_1110_, v___x_1111_);
v___x_1113_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1108_, v___x_1112_, v_i_1109_, v_var_1016_, v___x_1106_);
lean_dec(v_i_1109_);
v___y_1101_ = v___x_1113_;
goto v___jp_1100_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_1115_, v_var_1016_);
switch(lean_obj_tag(v___x_1116_))
{
case 0:
{
lean_object* v_index_1117_; lean_object* v_size_1118_; lean_object* v___x_1119_; 
v_index_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_index_1117_);
lean_dec_ref_known(v___x_1116_, 3);
v_size_1118_ = lean_ctor_get(v___y_1115_, 0);
lean_inc(v_size_1118_);
v___x_1119_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1115_, v_size_1118_, v_index_1117_, v_var_1016_, v___x_1106_);
lean_dec(v_index_1117_);
v___y_1101_ = v___x_1119_;
goto v___jp_1100_;
}
case 1:
{
lean_object* v_index_1120_; 
v_index_1120_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_index_1120_);
lean_dec_ref_known(v___x_1116_, 1);
v___y_1108_ = v___y_1115_;
v_i_1109_ = v_index_1120_;
goto v___jp_1107_;
}
default: 
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1115_, v___x_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_index_1123_; 
v_index_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_index_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___y_1108_ = v___y_1115_;
v_i_1109_ = v_index_1123_;
goto v___jp_1107_;
}
else
{
lean_dec(v_var_1016_);
v___y_1101_ = v___y_1115_;
goto v___jp_1100_;
}
}
}
}
v___jp_1124_:
{
lean_object* v_size_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_size_1127_ = lean_ctor_get(v___y_1125_, 0);
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_size_1127_, v___x_1128_);
v___x_1130_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1125_, v___x_1129_, v_i_1126_, v_var_1016_, v___x_1106_);
lean_dec(v_i_1126_);
v___y_1101_ = v___x_1130_;
goto v___jp_1100_;
}
v___jp_1131_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___x_1098_);
lean_dec(v___x_1098_);
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_1132_, v_var_1016_);
switch(lean_obj_tag(v___x_1133_))
{
case 0:
{
lean_object* v_index_1134_; lean_object* v_size_1135_; lean_object* v___x_1136_; 
v_index_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_index_1134_);
lean_dec_ref_known(v___x_1133_, 3);
v_size_1135_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_size_1135_);
v___x_1136_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1132_, v_size_1135_, v_index_1134_, v_var_1016_, v___x_1106_);
lean_dec(v_index_1134_);
v___y_1101_ = v___x_1136_;
goto v___jp_1100_;
}
case 1:
{
lean_object* v_index_1137_; 
v_index_1137_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_index_1137_);
lean_dec_ref_known(v___x_1133_, 1);
v___y_1125_ = v___x_1132_;
v_i_1126_ = v_index_1137_;
goto v___jp_1124_;
}
default: 
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1132_, v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_index_1140_; 
v_index_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_index_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___y_1125_ = v___x_1132_;
v_i_1126_ = v_index_1140_;
goto v___jp_1124_;
}
else
{
lean_dec(v_var_1016_);
v___y_1101_ = v___x_1132_;
goto v___jp_1100_;
}
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec(v_var_1016_);
v___x_1171_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1171_);
v___x_1173_ = v___x_1023_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec(v___x_1020_);
lean_dec(v_var_1016_);
lean_dec(v_plannedDecision_1015_);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_1178_, lean_object* v_var_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1178_, v_var_1179_, v_a_1180_);
lean_dec(v_a_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_1183_, lean_object* v_var_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1183_, v_var_1184_, v_a_1185_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_1193_, lean_object* v_var_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1193_, v_var_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec(v_a_1195_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_1203_, lean_object* v_m_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1204_, v_a_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1207_, lean_object* v_m_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1207_, v_m_1208_, v_a_1209_);
lean_dec(v_a_1209_);
lean_dec_ref(v_m_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1211_, lean_object* v_f_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
switch(lean_obj_tag(v_alt_1211_))
{
case 0:
{
lean_object* v_code_1220_; lean_object* v___x_1221_; 
v_code_1220_ = lean_ctor_get(v_alt_1211_, 2);
lean_inc_ref(v_code_1220_);
lean_dec_ref_known(v_alt_1211_, 3);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___y_1213_);
v___x_1221_ = lean_apply_8(v_f_1212_, v_code_1220_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1221_;
}
case 1:
{
lean_object* v_code_1222_; lean_object* v___x_1223_; 
v_code_1222_ = lean_ctor_get(v_alt_1211_, 1);
lean_inc_ref(v_code_1222_);
lean_dec_ref_known(v_alt_1211_, 2);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___y_1213_);
v___x_1223_ = lean_apply_8(v_f_1212_, v_code_1222_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1223_;
}
default: 
{
lean_object* v_code_1224_; lean_object* v___x_1225_; 
v_code_1224_ = lean_ctor_get(v_alt_1211_, 0);
lean_inc_ref(v_code_1224_);
lean_dec_ref_known(v_alt_1211_, 1);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___y_1213_);
v___x_1225_ = lean_apply_8(v_f_1212_, v_code_1224_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1226_, lean_object* v_f_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1226_, v_f_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
return v_res_1235_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_instMonadEIO(lean_box(0));
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_toApplicative_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1314_; 
v___x_1249_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1250_ = l_StateRefT_x27_instMonad___redArg(v___x_1249_);
v_toApplicative_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1250_, 1);
lean_dec(v_unused_1315_);
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1314_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_toApplicative_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1314_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_toFunctor_1255_; lean_object* v_toSeq_1256_; lean_object* v_toSeqLeft_1257_; lean_object* v_toSeqRight_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1312_; 
v_toFunctor_1255_ = lean_ctor_get(v_toApplicative_1251_, 0);
v_toSeq_1256_ = lean_ctor_get(v_toApplicative_1251_, 2);
v_toSeqLeft_1257_ = lean_ctor_get(v_toApplicative_1251_, 3);
v_toSeqRight_1258_ = lean_ctor_get(v_toApplicative_1251_, 4);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_toApplicative_1251_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_toApplicative_1251_, 1);
lean_dec(v_unused_1313_);
v___x_1260_ = v_toApplicative_1251_;
v_isShared_1261_ = v_isSharedCheck_1312_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_toSeqRight_1258_);
lean_inc(v_toSeqLeft_1257_);
lean_inc(v_toSeq_1256_);
lean_inc(v_toFunctor_1255_);
lean_dec(v_toApplicative_1251_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1312_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1271_; 
v___f_1262_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1263_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1255_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toFunctor_1255_);
v___f_1265_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1265_, 0, v_toFunctor_1255_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___f_1264_);
lean_ctor_set(v___x_1266_, 1, v___f_1265_);
v___f_1267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1267_, 0, v_toSeqRight_1258_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toSeqLeft_1257_);
v___f_1269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1269_, 0, v_toSeq_1256_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 4, v___f_1267_);
lean_ctor_set(v___x_1260_, 3, v___f_1268_);
lean_ctor_set(v___x_1260_, 2, v___f_1269_);
lean_ctor_set(v___x_1260_, 1, v___f_1262_);
lean_ctor_set(v___x_1260_, 0, v___x_1266_);
v___x_1271_ = v___x_1260_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___f_1262_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v___f_1269_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v___f_1268_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v___f_1267_);
v___x_1271_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___f_1263_);
lean_ctor_set(v___x_1253_, 0, v___x_1271_);
v___x_1273_ = v___x_1253_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___f_1263_);
v___x_1273_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v_toApplicative_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1308_; 
v___x_1274_ = l_StateRefT_x27_instMonad___redArg(v___x_1273_);
v_toApplicative_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1274_, 1);
lean_dec(v_unused_1309_);
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1308_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_toApplicative_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1308_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_toFunctor_1279_; lean_object* v_toSeq_1280_; lean_object* v_toSeqLeft_1281_; lean_object* v_toSeqRight_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1306_; 
v_toFunctor_1279_ = lean_ctor_get(v_toApplicative_1275_, 0);
v_toSeq_1280_ = lean_ctor_get(v_toApplicative_1275_, 2);
v_toSeqLeft_1281_ = lean_ctor_get(v_toApplicative_1275_, 3);
v_toSeqRight_1282_ = lean_ctor_get(v_toApplicative_1275_, 4);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_toApplicative_1275_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_toApplicative_1275_, 1);
lean_dec(v_unused_1307_);
v___x_1284_ = v_toApplicative_1275_;
v_isShared_1285_ = v_isSharedCheck_1306_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_toSeqRight_1282_);
lean_inc(v_toSeqLeft_1281_);
lean_inc(v_toSeq_1280_);
lean_inc(v_toFunctor_1279_);
lean_dec(v_toApplicative_1275_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1306_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___x_1295_; 
v___f_1286_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1287_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1279_);
v___f_1288_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1288_, 0, v_toFunctor_1279_);
v___f_1289_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1289_, 0, v_toFunctor_1279_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___f_1288_);
lean_ctor_set(v___x_1290_, 1, v___f_1289_);
v___f_1291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1291_, 0, v_toSeqRight_1282_);
v___f_1292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1292_, 0, v_toSeqLeft_1281_);
v___f_1293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1293_, 0, v_toSeq_1280_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 4, v___f_1291_);
lean_ctor_set(v___x_1284_, 3, v___f_1292_);
lean_ctor_set(v___x_1284_, 2, v___f_1293_);
lean_ctor_set(v___x_1284_, 1, v___f_1286_);
lean_ctor_set(v___x_1284_, 0, v___x_1290_);
v___x_1295_ = v___x_1284_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___f_1286_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v___f_1293_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v___f_1292_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v___f_1291_);
v___x_1295_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1297_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___f_1287_);
lean_ctor_set(v___x_1277_, 0, v___x_1295_);
v___x_1297_ = v___x_1277_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___f_1287_);
v___x_1297_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_9302__overap_1302_; lean_object* v___x_1303_; 
v___x_1298_ = l_ReaderT_instMonad___redArg(v___x_1297_);
v___x_1299_ = l_StateRefT_x27_instMonad___redArg(v___x_1298_);
v___x_1300_ = lean_box(0);
v___x_1301_ = l_instInhabitedOfMonad___redArg(v___x_1299_, v___x_1300_);
v___x_9302__overap_1302_ = lean_panic_fn_borrowed(v___x_1301_, v_msg_1241_);
lean_dec(v___x_1301_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc(v___y_1242_);
v___x_1303_ = lean_apply_7(v___x_9302__overap_1302_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, lean_box(0));
return v___x_1303_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec(v___y_1317_);
return v_res_1324_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1328_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1329_ = lean_unsigned_to_nat(40u);
v___x_1330_ = lean_unsigned_to_nat(49u);
v___x_1331_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1332_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1333_ = l_mkPanicMessageWithDecl(v___x_1332_, v___x_1331_, v___x_1330_, v___x_1329_, v___x_1328_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1334_, lean_object* v_e_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_ty_1344_; lean_object* v_body_1345_; uint8_t v___x_1348_; 
v___x_1348_ = l_Lean_Expr_hasFVar(v_e_1335_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_e_1335_);
lean_dec_ref(v_f_1334_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
else
{
switch(lean_obj_tag(v_e_1335_))
{
case 1:
{
lean_object* v_fvarId_1351_; lean_object* v___x_1352_; 
v_fvarId_1351_ = lean_ctor_get(v_e_1335_, 0);
lean_inc(v_fvarId_1351_);
lean_dec_ref_known(v_e_1335_, 1);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc(v___y_1336_);
v___x_1352_ = lean_apply_8(v_f_1334_, v_fvarId_1351_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, lean_box(0));
return v___x_1352_;
}
case 2:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref_known(v_e_1335_, 1);
lean_dec_ref(v_f_1334_);
v___x_1353_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1354_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1353_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1354_;
}
case 5:
{
lean_object* v_fn_1355_; lean_object* v_arg_1356_; lean_object* v___x_1357_; 
v_fn_1355_ = lean_ctor_get(v_e_1335_, 0);
lean_inc_ref(v_fn_1355_);
v_arg_1356_ = lean_ctor_get(v_e_1335_, 1);
lean_inc_ref(v_arg_1356_);
lean_dec_ref_known(v_e_1335_, 2);
lean_inc_ref(v_f_1334_);
v___x_1357_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1334_, v_fn_1355_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v_e_1335_ = v_arg_1356_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1356_);
lean_dec_ref(v_f_1334_);
return v___x_1357_;
}
}
case 6:
{
lean_object* v_binderType_1359_; lean_object* v_body_1360_; 
v_binderType_1359_ = lean_ctor_get(v_e_1335_, 1);
lean_inc_ref(v_binderType_1359_);
v_body_1360_ = lean_ctor_get(v_e_1335_, 2);
lean_inc_ref(v_body_1360_);
lean_dec_ref_known(v_e_1335_, 3);
v_ty_1344_ = v_binderType_1359_;
v_body_1345_ = v_body_1360_;
goto v___jp_1343_;
}
case 7:
{
lean_object* v_binderType_1361_; lean_object* v_body_1362_; 
v_binderType_1361_ = lean_ctor_get(v_e_1335_, 1);
lean_inc_ref(v_binderType_1361_);
v_body_1362_ = lean_ctor_get(v_e_1335_, 2);
lean_inc_ref(v_body_1362_);
lean_dec_ref_known(v_e_1335_, 3);
v_ty_1344_ = v_binderType_1361_;
v_body_1345_ = v_body_1362_;
goto v___jp_1343_;
}
case 8:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec_ref_known(v_e_1335_, 4);
lean_dec_ref(v_f_1334_);
v___x_1363_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1364_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1363_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1364_;
}
case 11:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref_known(v_e_1335_, 3);
lean_dec_ref(v_f_1334_);
v___x_1365_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1366_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1365_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1366_;
}
default: 
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_e_1335_);
lean_dec_ref(v_f_1334_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
}
v___jp_1343_:
{
lean_object* v___x_1346_; 
lean_inc_ref(v_f_1334_);
v___x_1346_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1334_, v_ty_1344_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_dec_ref_known(v___x_1346_, 1);
v_e_1335_ = v_body_1345_;
goto _start;
}
else
{
lean_dec_ref(v_body_1345_);
lean_dec_ref(v_f_1334_);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1369_, lean_object* v_e_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1369_, v_e_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec(v___y_1371_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1379_, lean_object* v_arg_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
switch(lean_obj_tag(v_arg_1380_))
{
case 0:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_f_1379_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
case 1:
{
lean_object* v_fvarId_1390_; lean_object* v___x_1391_; 
v_fvarId_1390_ = lean_ctor_get(v_arg_1380_, 0);
lean_inc(v_fvarId_1390_);
lean_dec_ref_known(v_arg_1380_, 1);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc(v___y_1382_);
lean_inc(v___y_1381_);
v___x_1391_ = lean_apply_8(v_f_1379_, v_fvarId_1390_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, lean_box(0));
return v___x_1391_;
}
default: 
{
lean_object* v_expr_1392_; lean_object* v___x_1393_; 
v_expr_1392_ = lean_ctor_get(v_arg_1380_, 0);
lean_inc_ref(v_expr_1392_);
lean_dec_ref_known(v_arg_1380_, 1);
v___x_1393_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1379_, v_expr_1392_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1394_, lean_object* v_arg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1394_, v_arg_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1404_, lean_object* v_f_1405_, lean_object* v_as_1406_, size_t v_i_1407_, size_t v_stop_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1407_, v_stop_1408_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1406_, v_i_1407_);
lean_inc(v___x_1418_);
lean_inc_ref(v_f_1405_);
v___x_1419_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1405_, v___x_1418_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; size_t v___x_1421_; size_t v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1407_, v___x_1421_);
v_i_1407_ = v___x_1422_;
v_b_1409_ = v_a_1420_;
goto _start;
}
else
{
lean_dec_ref(v_f_1405_);
return v___x_1419_;
}
}
else
{
lean_object* v___x_1424_; 
lean_dec_ref(v_f_1405_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_b_1409_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1425_, lean_object* v_f_1426_, lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v_pu_boxed_1438_; size_t v_i_boxed_1439_; size_t v_stop_boxed_1440_; lean_object* v_res_1441_; 
v_pu_boxed_1438_ = lean_unbox(v_pu_1425_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1440_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1438_, v_f_1426_, v_as_1427_, v_i_boxed_1439_, v_stop_boxed_1440_, v_b_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v_as_1427_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1442_, lean_object* v_f_1443_, lean_object* v_e_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_args_1453_; 
switch(lean_obj_tag(v_e_1444_))
{
case 2:
{
lean_object* v_struct_1467_; lean_object* v___x_1468_; 
v_struct_1467_ = lean_ctor_get(v_e_1444_, 2);
lean_inc(v_struct_1467_);
lean_dec_ref_known(v_e_1444_, 3);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1468_ = lean_apply_8(v_f_1443_, v_struct_1467_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1468_;
}
case 3:
{
lean_object* v_args_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_args_1469_ = lean_ctor_get(v_e_1444_, 2);
lean_inc_ref(v_args_1469_);
lean_dec_ref_known(v_e_1444_, 3);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_array_get_size(v_args_1469_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_nat_dec_lt(v___x_1470_, v___x_1471_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_dec_ref(v_args_1469_);
lean_dec_ref(v_f_1443_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
return v___x_1474_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_nat_dec_le(v___x_1471_, v___x_1471_);
if (v___x_1475_ == 0)
{
if (v___x_1473_ == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref(v_args_1469_);
lean_dec_ref(v_f_1443_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1472_);
return v___x_1476_;
}
else
{
size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = lean_usize_of_nat(v___x_1471_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1469_, v___x_1477_, v___x_1478_, v___x_1472_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1469_);
return v___x_1479_;
}
}
else
{
size_t v___x_1480_; size_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = ((size_t)0ULL);
v___x_1481_ = lean_usize_of_nat(v___x_1471_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1469_, v___x_1480_, v___x_1481_, v___x_1472_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1469_);
return v___x_1482_;
}
}
}
case 4:
{
lean_object* v_fvarId_1483_; lean_object* v_args_1484_; lean_object* v___x_1485_; 
v_fvarId_1483_ = lean_ctor_get(v_e_1444_, 0);
lean_inc(v_fvarId_1483_);
v_args_1484_ = lean_ctor_get(v_e_1444_, 1);
lean_inc_ref(v_args_1484_);
lean_dec_ref_known(v_e_1444_, 2);
lean_inc_ref(v_f_1443_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1485_ = lean_apply_8(v_f_1443_, v_fvarId_1483_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1506_; 
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v___x_1485_, 0);
lean_dec(v_unused_1507_);
v___x_1487_ = v___x_1485_;
v_isShared_1488_ = v_isSharedCheck_1506_;
goto v_resetjp_1486_;
}
else
{
lean_dec(v___x_1485_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1506_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_array_get_size(v_args_1484_);
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_nat_dec_lt(v___x_1489_, v___x_1490_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1494_; 
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_f_1443_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1491_);
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1491_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_le(v___x_1490_, v___x_1490_);
if (v___x_1496_ == 0)
{
if (v___x_1492_ == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_f_1443_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1491_);
v___x_1498_ = v___x_1487_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1491_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
else
{
size_t v___x_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
lean_del_object(v___x_1487_);
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = lean_usize_of_nat(v___x_1490_);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1484_, v___x_1500_, v___x_1501_, v___x_1491_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1484_);
return v___x_1502_;
}
}
else
{
size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
lean_del_object(v___x_1487_);
v___x_1503_ = ((size_t)0ULL);
v___x_1504_ = lean_usize_of_nat(v___x_1490_);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1484_, v___x_1503_, v___x_1504_, v___x_1491_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1484_);
return v___x_1505_;
}
}
}
}
else
{
lean_dec_ref(v_args_1484_);
lean_dec_ref(v_f_1443_);
return v___x_1485_;
}
}
case 5:
{
lean_object* v_args_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_args_1508_ = lean_ctor_get(v_e_1444_, 1);
lean_inc_ref(v_args_1508_);
lean_dec_ref_known(v_e_1444_, 2);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_get_size(v_args_1508_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_nat_dec_lt(v___x_1509_, v___x_1510_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v_args_1508_);
lean_dec_ref(v_f_1443_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
return v___x_1513_;
}
else
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_le(v___x_1510_, v___x_1510_);
if (v___x_1514_ == 0)
{
if (v___x_1512_ == 0)
{
lean_object* v___x_1515_; 
lean_dec_ref(v_args_1508_);
lean_dec_ref(v_f_1443_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1511_);
return v___x_1515_;
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1510_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1508_, v___x_1516_, v___x_1517_, v___x_1511_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1508_);
return v___x_1518_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1510_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1508_, v___x_1519_, v___x_1520_, v___x_1511_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1508_);
return v___x_1521_;
}
}
}
case 6:
{
lean_object* v_var_1522_; lean_object* v___x_1523_; 
v_var_1522_ = lean_ctor_get(v_e_1444_, 1);
lean_inc(v_var_1522_);
lean_dec_ref_known(v_e_1444_, 2);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1523_ = lean_apply_8(v_f_1443_, v_var_1522_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1523_;
}
case 7:
{
lean_object* v_var_1524_; lean_object* v___x_1525_; 
v_var_1524_ = lean_ctor_get(v_e_1444_, 1);
lean_inc(v_var_1524_);
lean_dec_ref_known(v_e_1444_, 2);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1525_ = lean_apply_8(v_f_1443_, v_var_1524_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1525_;
}
case 8:
{
lean_object* v_var_1526_; lean_object* v___x_1527_; 
v_var_1526_ = lean_ctor_get(v_e_1444_, 2);
lean_inc(v_var_1526_);
lean_dec_ref_known(v_e_1444_, 3);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1527_ = lean_apply_8(v_f_1443_, v_var_1526_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1527_;
}
case 9:
{
lean_object* v_args_1528_; 
v_args_1528_ = lean_ctor_get(v_e_1444_, 1);
lean_inc_ref(v_args_1528_);
lean_dec_ref_known(v_e_1444_, 2);
v_args_1453_ = v_args_1528_;
goto v___jp_1452_;
}
case 10:
{
lean_object* v_args_1529_; 
v_args_1529_ = lean_ctor_get(v_e_1444_, 1);
lean_inc_ref(v_args_1529_);
lean_dec_ref_known(v_e_1444_, 2);
v_args_1453_ = v_args_1529_;
goto v___jp_1452_;
}
case 11:
{
lean_object* v_var_1530_; lean_object* v___x_1531_; 
v_var_1530_ = lean_ctor_get(v_e_1444_, 1);
lean_inc(v_var_1530_);
lean_dec_ref_known(v_e_1444_, 2);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1531_ = lean_apply_8(v_f_1443_, v_var_1530_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1531_;
}
case 12:
{
lean_object* v_var_1532_; lean_object* v_args_1533_; lean_object* v___x_1534_; 
v_var_1532_ = lean_ctor_get(v_e_1444_, 0);
lean_inc(v_var_1532_);
v_args_1533_ = lean_ctor_get(v_e_1444_, 2);
lean_inc_ref(v_args_1533_);
lean_dec_ref_known(v_e_1444_, 3);
lean_inc_ref(v_f_1443_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1534_ = lean_apply_8(v_f_1443_, v_var_1532_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1555_; 
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v___x_1534_, 0);
lean_dec(v_unused_1556_);
v___x_1536_ = v___x_1534_;
v_isShared_1537_ = v_isSharedCheck_1555_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v___x_1534_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1555_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_array_get_size(v_args_1533_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1543_; 
lean_dec_ref(v_args_1533_);
lean_dec_ref(v_f_1443_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1540_);
v___x_1543_ = v___x_1536_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1540_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_nat_dec_le(v___x_1539_, v___x_1539_);
if (v___x_1545_ == 0)
{
if (v___x_1541_ == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref(v_args_1533_);
lean_dec_ref(v_f_1443_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1540_);
v___x_1547_ = v___x_1536_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
lean_del_object(v___x_1536_);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = lean_usize_of_nat(v___x_1539_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1533_, v___x_1549_, v___x_1550_, v___x_1540_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1533_);
return v___x_1551_;
}
}
else
{
size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
lean_del_object(v___x_1536_);
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = lean_usize_of_nat(v___x_1539_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1533_, v___x_1552_, v___x_1553_, v___x_1540_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1533_);
return v___x_1554_;
}
}
}
}
else
{
lean_dec_ref(v_args_1533_);
lean_dec_ref(v_f_1443_);
return v___x_1534_;
}
}
case 13:
{
lean_object* v_fvarId_1557_; lean_object* v___x_1558_; 
v_fvarId_1557_ = lean_ctor_get(v_e_1444_, 1);
lean_inc(v_fvarId_1557_);
lean_dec_ref_known(v_e_1444_, 2);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1558_ = lean_apply_8(v_f_1443_, v_fvarId_1557_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1558_;
}
case 14:
{
lean_object* v_fvarId_1559_; lean_object* v___x_1560_; 
v_fvarId_1559_ = lean_ctor_get(v_e_1444_, 0);
lean_inc(v_fvarId_1559_);
lean_dec_ref_known(v_e_1444_, 1);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1560_ = lean_apply_8(v_f_1443_, v_fvarId_1559_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1560_;
}
case 15:
{
lean_object* v_fvarId_1561_; lean_object* v___x_1562_; 
v_fvarId_1561_ = lean_ctor_get(v_e_1444_, 0);
lean_inc(v_fvarId_1561_);
lean_dec_ref_known(v_e_1444_, 1);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1562_ = lean_apply_8(v_f_1443_, v_fvarId_1561_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1562_;
}
default: 
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v_e_1444_);
lean_dec_ref(v_f_1443_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
v___jp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_array_get_size(v_args_1453_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
lean_dec_ref(v_args_1453_);
lean_dec_ref(v_f_1443_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
return v___x_1458_;
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_nat_dec_le(v___x_1455_, v___x_1455_);
if (v___x_1459_ == 0)
{
if (v___x_1457_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_args_1453_);
lean_dec_ref(v_f_1443_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1456_);
return v___x_1460_;
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1455_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1453_, v___x_1461_, v___x_1462_, v___x_1456_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1453_);
return v___x_1463_;
}
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1455_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1442_, v_f_1443_, v_args_1453_, v___x_1464_, v___x_1465_, v___x_1456_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v_args_1453_);
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1565_, lean_object* v_f_1566_, lean_object* v_e_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_pu_boxed_1575_; lean_object* v_res_1576_; 
v_pu_boxed_1575_ = lean_unbox(v_pu_1565_);
v_res_1576_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1575_, v_f_1566_, v_e_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1577_, lean_object* v_f_1578_, lean_object* v_decl_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_type_1587_; lean_object* v_value_1588_; lean_object* v___x_1589_; 
v_type_1587_ = lean_ctor_get(v_decl_1579_, 2);
lean_inc_ref(v_type_1587_);
v_value_1588_ = lean_ctor_get(v_decl_1579_, 3);
lean_inc(v_value_1588_);
lean_dec_ref(v_decl_1579_);
lean_inc_ref(v_f_1578_);
v___x_1589_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1578_, v_type_1587_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref_known(v___x_1589_, 1);
v___x_1590_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1577_, v_f_1578_, v_value_1588_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1590_;
}
else
{
lean_dec(v_value_1588_);
lean_dec_ref(v_f_1578_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1591_, lean_object* v_f_1592_, lean_object* v_decl_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_pu_boxed_1601_; lean_object* v_res_1602_; 
v_pu_boxed_1601_ = lean_unbox(v_pu_1591_);
v_res_1602_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1601_, v_f_1592_, v_decl_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1603_, lean_object* v_param_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_type_1612_; lean_object* v___x_1613_; 
v_type_1612_ = lean_ctor_get(v_param_1604_, 2);
lean_inc_ref(v_type_1612_);
lean_dec_ref(v_param_1604_);
v___x_1613_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1603_, v_type_1612_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1614_, lean_object* v_param_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1614_, v_param_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec(v___y_1616_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1624_, lean_object* v_f_1625_, lean_object* v_as_1626_, size_t v_i_1627_, size_t v_stop_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_usize_dec_eq(v_i_1627_, v_stop_1628_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_array_uget_borrowed(v_as_1626_, v_i_1627_);
lean_inc(v___x_1638_);
lean_inc_ref(v_f_1625_);
v___x_1639_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1625_, v___x_1638_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; size_t v___x_1641_; size_t v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = ((size_t)1ULL);
v___x_1642_ = lean_usize_add(v_i_1627_, v___x_1641_);
v_i_1627_ = v___x_1642_;
v_b_1629_ = v_a_1640_;
goto _start;
}
else
{
lean_dec_ref(v_f_1625_);
return v___x_1639_;
}
}
else
{
lean_object* v___x_1644_; 
lean_dec_ref(v_f_1625_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_b_1629_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1645_, lean_object* v_f_1646_, lean_object* v_as_1647_, lean_object* v_i_1648_, lean_object* v_stop_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
uint8_t v_pu_boxed_1658_; size_t v_i_boxed_1659_; size_t v_stop_boxed_1660_; lean_object* v_res_1661_; 
v_pu_boxed_1658_ = lean_unbox(v_pu_1645_);
v_i_boxed_1659_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_stop_boxed_1660_ = lean_unbox_usize(v_stop_1649_);
lean_dec(v_stop_1649_);
v_res_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1658_, v_f_1646_, v_as_1647_, v_i_boxed_1659_, v_stop_boxed_1660_, v_b_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v_as_1647_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1662_, lean_object* v_f_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v_pu_boxed_1672_; lean_object* v_res_1673_; 
v_pu_boxed_1672_ = lean_unbox(v_pu_1662_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1672_, v_f_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec(v___y_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1674_, lean_object* v_f_1675_, lean_object* v_as_1676_, size_t v_i_1677_, size_t v_stop_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_eq(v_i_1677_, v_stop_1678_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1688_ = lean_box(v_pu_1674_);
lean_inc_ref(v_f_1675_);
v___f_1689_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1689_, 0, v___x_1688_);
lean_closure_set(v___f_1689_, 1, v_f_1675_);
v___x_1690_ = lean_array_uget_borrowed(v_as_1676_, v_i_1677_);
lean_inc(v___x_1690_);
v___x_1691_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1690_, v___f_1689_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; size_t v___x_1693_; size_t v___x_1694_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_add(v_i_1677_, v___x_1693_);
v_i_1677_ = v___x_1694_;
v_b_1679_ = v_a_1692_;
goto _start;
}
else
{
lean_dec_ref(v_f_1675_);
return v___x_1691_;
}
}
else
{
lean_object* v___x_1696_; 
lean_dec_ref(v_f_1675_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_b_1679_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1697_, lean_object* v_f_1698_, lean_object* v_c_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
switch(lean_obj_tag(v_c_1699_))
{
case 0:
{
lean_object* v_decl_1707_; lean_object* v_k_1708_; lean_object* v___x_1709_; 
v_decl_1707_ = lean_ctor_get(v_c_1699_, 0);
lean_inc_ref(v_decl_1707_);
v_k_1708_ = lean_ctor_get(v_c_1699_, 1);
lean_inc_ref(v_k_1708_);
lean_dec_ref_known(v_c_1699_, 2);
lean_inc_ref(v_f_1698_);
v___x_1709_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1697_, v_f_1698_, v_decl_1707_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_dec_ref_known(v___x_1709_, 1);
v_c_1699_ = v_k_1708_;
goto _start;
}
else
{
lean_dec_ref(v_k_1708_);
lean_dec_ref(v_f_1698_);
return v___x_1709_;
}
}
case 3:
{
lean_object* v_fvarId_1711_; lean_object* v_args_1712_; lean_object* v___x_1713_; 
v_fvarId_1711_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1711_);
v_args_1712_ = lean_ctor_get(v_c_1699_, 1);
lean_inc_ref(v_args_1712_);
lean_dec_ref_known(v_c_1699_, 2);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1713_ = lean_apply_8(v_f_1698_, v_fvarId_1711_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1734_; 
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1713_, 0);
lean_dec(v_unused_1735_);
v___x_1715_ = v___x_1713_;
v_isShared_1716_ = v_isSharedCheck_1734_;
goto v_resetjp_1714_;
}
else
{
lean_dec(v___x_1713_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1734_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_array_get_size(v_args_1712_);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_nat_dec_lt(v___x_1717_, v___x_1718_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref(v_args_1712_);
lean_dec_ref(v_f_1698_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1719_);
v___x_1722_ = v___x_1715_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1719_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
else
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_nat_dec_le(v___x_1718_, v___x_1718_);
if (v___x_1724_ == 0)
{
if (v___x_1720_ == 0)
{
lean_object* v___x_1726_; 
lean_dec_ref(v_args_1712_);
lean_dec_ref(v_f_1698_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1719_);
v___x_1726_ = v___x_1715_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1719_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
else
{
size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
lean_del_object(v___x_1715_);
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = lean_usize_of_nat(v___x_1718_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1697_, v_f_1698_, v_args_1712_, v___x_1728_, v___x_1729_, v___x_1719_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_args_1712_);
return v___x_1730_;
}
}
else
{
size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
lean_del_object(v___x_1715_);
v___x_1731_ = ((size_t)0ULL);
v___x_1732_ = lean_usize_of_nat(v___x_1718_);
v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1697_, v_f_1698_, v_args_1712_, v___x_1731_, v___x_1732_, v___x_1719_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_args_1712_);
return v___x_1733_;
}
}
}
}
else
{
lean_dec_ref(v_args_1712_);
lean_dec_ref(v_f_1698_);
return v___x_1713_;
}
}
case 4:
{
lean_object* v_cases_1736_; lean_object* v_resultType_1737_; lean_object* v_discr_1738_; lean_object* v_alts_1739_; lean_object* v___x_1740_; 
v_cases_1736_ = lean_ctor_get(v_c_1699_, 0);
lean_inc_ref(v_cases_1736_);
lean_dec_ref_known(v_c_1699_, 1);
v_resultType_1737_ = lean_ctor_get(v_cases_1736_, 1);
lean_inc_ref(v_resultType_1737_);
v_discr_1738_ = lean_ctor_get(v_cases_1736_, 2);
lean_inc(v_discr_1738_);
v_alts_1739_ = lean_ctor_get(v_cases_1736_, 3);
lean_inc_ref(v_alts_1739_);
lean_dec_ref(v_cases_1736_);
lean_inc_ref(v_f_1698_);
v___x_1740_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1698_, v_resultType_1737_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref_known(v___x_1740_, 1);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1741_ = lean_apply_8(v_f_1698_, v_discr_1738_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1762_; 
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1763_);
v___x_1743_ = v___x_1741_;
v_isShared_1744_ = v_isSharedCheck_1762_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v___x_1741_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1762_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_array_get_size(v_alts_1739_);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1750_; 
lean_dec_ref(v_alts_1739_);
lean_dec_ref(v_f_1698_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1747_);
v___x_1750_ = v___x_1743_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1747_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
else
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_nat_dec_le(v___x_1746_, v___x_1746_);
if (v___x_1752_ == 0)
{
if (v___x_1748_ == 0)
{
lean_object* v___x_1754_; 
lean_dec_ref(v_alts_1739_);
lean_dec_ref(v_f_1698_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1747_);
v___x_1754_ = v___x_1743_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1747_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
else
{
size_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
lean_del_object(v___x_1743_);
v___x_1756_ = ((size_t)0ULL);
v___x_1757_ = lean_usize_of_nat(v___x_1746_);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1697_, v_f_1698_, v_alts_1739_, v___x_1756_, v___x_1757_, v___x_1747_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_alts_1739_);
return v___x_1758_;
}
}
else
{
size_t v___x_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
lean_del_object(v___x_1743_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = lean_usize_of_nat(v___x_1746_);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1697_, v_f_1698_, v_alts_1739_, v___x_1759_, v___x_1760_, v___x_1747_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_alts_1739_);
return v___x_1761_;
}
}
}
}
else
{
lean_dec_ref(v_alts_1739_);
lean_dec_ref(v_f_1698_);
return v___x_1741_;
}
}
else
{
lean_dec_ref(v_alts_1739_);
lean_dec(v_discr_1738_);
lean_dec_ref(v_f_1698_);
return v___x_1740_;
}
}
case 5:
{
lean_object* v_fvarId_1764_; lean_object* v___x_1765_; 
v_fvarId_1764_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1764_);
lean_dec_ref_known(v_c_1699_, 1);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1765_ = lean_apply_8(v_f_1698_, v_fvarId_1764_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
return v___x_1765_;
}
case 6:
{
lean_object* v_type_1766_; lean_object* v___x_1767_; 
v_type_1766_ = lean_ctor_get(v_c_1699_, 0);
lean_inc_ref(v_type_1766_);
lean_dec_ref_known(v_c_1699_, 1);
v___x_1767_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1698_, v_type_1766_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1767_;
}
case 7:
{
lean_object* v_fvarId_1768_; lean_object* v_y_1769_; lean_object* v_k_1770_; lean_object* v___x_1771_; 
v_fvarId_1768_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1768_);
v_y_1769_ = lean_ctor_get(v_c_1699_, 2);
lean_inc(v_y_1769_);
v_k_1770_ = lean_ctor_get(v_c_1699_, 3);
lean_inc_ref(v_k_1770_);
lean_dec_ref_known(v_c_1699_, 4);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1771_ = lean_apply_8(v_f_1698_, v_fvarId_1768_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref_known(v___x_1771_, 1);
lean_inc_ref(v_f_1698_);
v___x_1772_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1698_, v_y_1769_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref_known(v___x_1772_, 1);
v_c_1699_ = v_k_1770_;
goto _start;
}
else
{
lean_dec_ref(v_k_1770_);
lean_dec_ref(v_f_1698_);
return v___x_1772_;
}
}
else
{
lean_dec_ref(v_k_1770_);
lean_dec(v_y_1769_);
lean_dec_ref(v_f_1698_);
return v___x_1771_;
}
}
case 8:
{
lean_object* v_fvarId_1774_; lean_object* v_y_1775_; lean_object* v_k_1776_; lean_object* v___x_1777_; 
v_fvarId_1774_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1774_);
v_y_1775_ = lean_ctor_get(v_c_1699_, 2);
lean_inc(v_y_1775_);
v_k_1776_ = lean_ctor_get(v_c_1699_, 3);
lean_inc_ref(v_k_1776_);
lean_dec_ref_known(v_c_1699_, 4);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1777_ = lean_apply_8(v_f_1698_, v_fvarId_1774_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v___x_1777_, 1);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1778_ = lean_apply_8(v_f_1698_, v_y_1775_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec_ref_known(v___x_1778_, 1);
v_c_1699_ = v_k_1776_;
goto _start;
}
else
{
lean_dec_ref(v_k_1776_);
lean_dec_ref(v_f_1698_);
return v___x_1778_;
}
}
else
{
lean_dec_ref(v_k_1776_);
lean_dec(v_y_1775_);
lean_dec_ref(v_f_1698_);
return v___x_1777_;
}
}
case 9:
{
lean_object* v_fvarId_1780_; lean_object* v_y_1781_; lean_object* v_ty_1782_; lean_object* v_k_1783_; lean_object* v___x_1784_; 
v_fvarId_1780_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1780_);
v_y_1781_ = lean_ctor_get(v_c_1699_, 3);
lean_inc(v_y_1781_);
v_ty_1782_ = lean_ctor_get(v_c_1699_, 4);
lean_inc_ref(v_ty_1782_);
v_k_1783_ = lean_ctor_get(v_c_1699_, 5);
lean_inc_ref(v_k_1783_);
lean_dec_ref_known(v_c_1699_, 6);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1784_ = lean_apply_8(v_f_1698_, v_fvarId_1780_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v___x_1785_; 
lean_dec_ref_known(v___x_1784_, 1);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1785_ = lean_apply_8(v_f_1698_, v_y_1781_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v___x_1785_, 1);
lean_inc_ref(v_f_1698_);
v___x_1786_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1698_, v_ty_1782_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_dec_ref_known(v___x_1786_, 1);
v_c_1699_ = v_k_1783_;
goto _start;
}
else
{
lean_dec_ref(v_k_1783_);
lean_dec_ref(v_f_1698_);
return v___x_1786_;
}
}
else
{
lean_dec_ref(v_k_1783_);
lean_dec_ref(v_ty_1782_);
lean_dec_ref(v_f_1698_);
return v___x_1785_;
}
}
else
{
lean_dec_ref(v_k_1783_);
lean_dec_ref(v_ty_1782_);
lean_dec(v_y_1781_);
lean_dec_ref(v_f_1698_);
return v___x_1784_;
}
}
case 10:
{
lean_object* v_fvarId_1788_; lean_object* v_k_1789_; lean_object* v___x_1790_; 
v_fvarId_1788_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1788_);
v_k_1789_ = lean_ctor_get(v_c_1699_, 2);
lean_inc_ref(v_k_1789_);
lean_dec_ref_known(v_c_1699_, 3);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1790_ = lean_apply_8(v_f_1698_, v_fvarId_1788_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec_ref_known(v___x_1790_, 1);
v_c_1699_ = v_k_1789_;
goto _start;
}
else
{
lean_dec_ref(v_k_1789_);
lean_dec_ref(v_f_1698_);
return v___x_1790_;
}
}
case 11:
{
lean_object* v_fvarId_1792_; lean_object* v_k_1793_; lean_object* v___x_1794_; 
v_fvarId_1792_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1792_);
v_k_1793_ = lean_ctor_get(v_c_1699_, 2);
lean_inc_ref(v_k_1793_);
lean_dec_ref_known(v_c_1699_, 3);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1794_ = lean_apply_8(v_f_1698_, v_fvarId_1792_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_dec_ref_known(v___x_1794_, 1);
v_c_1699_ = v_k_1793_;
goto _start;
}
else
{
lean_dec_ref(v_k_1793_);
lean_dec_ref(v_f_1698_);
return v___x_1794_;
}
}
case 12:
{
lean_object* v_fvarId_1796_; lean_object* v_k_1797_; lean_object* v___x_1798_; 
v_fvarId_1796_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1796_);
v_k_1797_ = lean_ctor_get(v_c_1699_, 3);
lean_inc_ref(v_k_1797_);
lean_dec_ref_known(v_c_1699_, 4);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1798_ = lean_apply_8(v_f_1698_, v_fvarId_1796_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_dec_ref_known(v___x_1798_, 1);
v_c_1699_ = v_k_1797_;
goto _start;
}
else
{
lean_dec_ref(v_k_1797_);
lean_dec_ref(v_f_1698_);
return v___x_1798_;
}
}
case 13:
{
lean_object* v_fvarId_1800_; lean_object* v_k_1801_; lean_object* v___x_1802_; 
v_fvarId_1800_ = lean_ctor_get(v_c_1699_, 0);
lean_inc(v_fvarId_1800_);
v_k_1801_ = lean_ctor_get(v_c_1699_, 1);
lean_inc_ref(v_k_1801_);
lean_dec_ref_known(v_c_1699_, 2);
lean_inc_ref(v_f_1698_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1802_ = lean_apply_8(v_f_1698_, v_fvarId_1800_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref_known(v___x_1802_, 1);
v_c_1699_ = v_k_1801_;
goto _start;
}
else
{
lean_dec_ref(v_k_1801_);
lean_dec_ref(v_f_1698_);
return v___x_1802_;
}
}
default: 
{
lean_object* v_decl_1804_; lean_object* v_k_1805_; lean_object* v_params_1806_; lean_object* v_type_1807_; lean_object* v_value_1808_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_decl_1804_ = lean_ctor_get(v_c_1699_, 0);
lean_inc_ref(v_decl_1804_);
v_k_1805_ = lean_ctor_get(v_c_1699_, 1);
lean_inc_ref(v_k_1805_);
lean_dec_ref(v_c_1699_);
v_params_1806_ = lean_ctor_get(v_decl_1804_, 2);
lean_inc_ref(v_params_1806_);
v_type_1807_ = lean_ctor_get(v_decl_1804_, 3);
lean_inc_ref(v_type_1807_);
v_value_1808_ = lean_ctor_get(v_decl_1804_, 4);
lean_inc_ref(v_value_1808_);
lean_dec_ref(v_decl_1804_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_array_get_size(v_params_1806_);
v___x_1821_ = lean_nat_dec_lt(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref(v_params_1806_);
lean_inc_ref(v_f_1698_);
v___x_1822_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1698_, v_type_1807_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v___x_1823_; 
lean_dec_ref_known(v___x_1822_, 1);
lean_inc_ref(v_f_1698_);
v___x_1823_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1697_, v_f_1698_, v_value_1808_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_dec_ref_known(v___x_1823_, 1);
v_c_1699_ = v_k_1805_;
goto _start;
}
else
{
lean_dec_ref(v_k_1805_);
lean_dec_ref(v_f_1698_);
return v___x_1823_;
}
}
else
{
lean_dec_ref(v_value_1808_);
lean_dec_ref(v_k_1805_);
lean_dec_ref(v_f_1698_);
return v___x_1822_;
}
}
else
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_nat_dec_le(v___x_1820_, v___x_1820_);
if (v___x_1826_ == 0)
{
if (v___x_1821_ == 0)
{
lean_dec_ref(v_params_1806_);
v___y_1810_ = v___y_1700_;
v___y_1811_ = v___y_1701_;
v___y_1812_ = v___y_1702_;
v___y_1813_ = v___y_1703_;
v___y_1814_ = v___y_1704_;
v___y_1815_ = v___y_1705_;
goto v___jp_1809_;
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = lean_usize_of_nat(v___x_1820_);
lean_inc_ref(v_f_1698_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1697_, v_f_1698_, v_params_1806_, v___x_1827_, v___x_1828_, v___x_1825_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_params_1806_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_dec_ref_known(v___x_1829_, 1);
v___y_1810_ = v___y_1700_;
v___y_1811_ = v___y_1701_;
v___y_1812_ = v___y_1702_;
v___y_1813_ = v___y_1703_;
v___y_1814_ = v___y_1704_;
v___y_1815_ = v___y_1705_;
goto v___jp_1809_;
}
else
{
lean_dec_ref(v_value_1808_);
lean_dec_ref(v_type_1807_);
lean_dec_ref(v_k_1805_);
lean_dec_ref(v_f_1698_);
return v___x_1829_;
}
}
}
else
{
size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = lean_usize_of_nat(v___x_1820_);
lean_inc_ref(v_f_1698_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1697_, v_f_1698_, v_params_1806_, v___x_1830_, v___x_1831_, v___x_1825_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_params_1806_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_dec_ref_known(v___x_1832_, 1);
v___y_1810_ = v___y_1700_;
v___y_1811_ = v___y_1701_;
v___y_1812_ = v___y_1702_;
v___y_1813_ = v___y_1703_;
v___y_1814_ = v___y_1704_;
v___y_1815_ = v___y_1705_;
goto v___jp_1809_;
}
else
{
lean_dec_ref(v_value_1808_);
lean_dec_ref(v_type_1807_);
lean_dec_ref(v_k_1805_);
lean_dec_ref(v_f_1698_);
return v___x_1832_;
}
}
}
v___jp_1809_:
{
lean_object* v___x_1816_; 
lean_inc_ref(v_f_1698_);
v___x_1816_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1698_, v_type_1807_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; 
lean_dec_ref_known(v___x_1816_, 1);
lean_inc_ref(v_f_1698_);
v___x_1817_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1697_, v_f_1698_, v_value_1808_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_dec_ref_known(v___x_1817_, 1);
v_c_1699_ = v_k_1805_;
v___y_1700_ = v___y_1810_;
v___y_1701_ = v___y_1811_;
v___y_1702_ = v___y_1812_;
v___y_1703_ = v___y_1813_;
v___y_1704_ = v___y_1814_;
v___y_1705_ = v___y_1815_;
goto _start;
}
else
{
lean_dec_ref(v_k_1805_);
lean_dec_ref(v_f_1698_);
return v___x_1817_;
}
}
else
{
lean_dec_ref(v_value_1808_);
lean_dec_ref(v_k_1805_);
lean_dec_ref(v_f_1698_);
return v___x_1816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1833_, lean_object* v_f_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1833_, v_f_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1844_, lean_object* v_f_1845_, lean_object* v_as_1846_, lean_object* v_i_1847_, lean_object* v_stop_1848_, lean_object* v_b_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v_pu_boxed_1857_; size_t v_i_boxed_1858_; size_t v_stop_boxed_1859_; lean_object* v_res_1860_; 
v_pu_boxed_1857_ = lean_unbox(v_pu_1844_);
v_i_boxed_1858_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_stop_boxed_1859_ = lean_unbox_usize(v_stop_1848_);
lean_dec(v_stop_1848_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1857_, v_f_1845_, v_as_1846_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v_as_1846_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1861_, lean_object* v_f_1862_, lean_object* v_c_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v_pu_boxed_1871_; lean_object* v_res_1872_; 
v_pu_boxed_1871_ = lean_unbox(v_pu_1861_);
v_res_1872_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1871_, v_f_1862_, v_c_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v___y_1864_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1873_, lean_object* v_as_1874_, size_t v_i_1875_, size_t v_stop_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_usize_dec_eq(v_i_1875_, v_stop_1876_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_inc(v___x_1873_);
v___x_1886_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1886_, 0, v___x_1873_);
v___x_1887_ = lean_array_uget_borrowed(v_as_1874_, v_i_1875_);
lean_inc(v___x_1887_);
v___x_1888_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1886_, v___x_1887_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; size_t v___x_1890_; size_t v___x_1891_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1875_, v___x_1890_);
v_i_1875_ = v___x_1891_;
v_b_1877_ = v_a_1889_;
goto _start;
}
else
{
lean_dec(v___x_1873_);
return v___x_1888_;
}
}
else
{
lean_object* v___x_1893_; 
lean_dec(v___x_1873_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_b_1877_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1894_, lean_object* v_as_1895_, lean_object* v_i_1896_, lean_object* v_stop_1897_, lean_object* v_b_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
size_t v_i_boxed_1906_; size_t v_stop_boxed_1907_; lean_object* v_res_1908_; 
v_i_boxed_1906_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_stop_boxed_1907_ = lean_unbox_usize(v_stop_1897_);
lean_dec(v_stop_1897_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1894_, v_as_1895_, v_i_boxed_1906_, v_stop_boxed_1907_, v_b_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v_as_1895_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = 0;
v___x_1918_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1909_);
lean_inc(v___x_1918_);
v___x_1919_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1919_, 0, v___x_1918_);
switch(lean_obj_tag(v_alt_1909_))
{
case 0:
{
lean_object* v_params_1920_; lean_object* v_code_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_params_1920_ = lean_ctor_get(v_alt_1909_, 1);
lean_inc_ref(v_params_1920_);
v_code_1921_ = lean_ctor_get(v_alt_1909_, 2);
lean_inc_ref(v_code_1921_);
lean_dec_ref_known(v_alt_1909_, 3);
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_array_get_size(v_params_1920_);
v___x_1924_ = lean_nat_dec_lt(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v_params_1920_);
lean_dec(v___x_1918_);
v___x_1925_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1917_, v___x_1919_, v_code_1921_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_nat_dec_le(v___x_1923_, v___x_1923_);
if (v___x_1927_ == 0)
{
if (v___x_1924_ == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref(v_params_1920_);
lean_dec(v___x_1918_);
v___x_1928_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1917_, v___x_1919_, v_code_1921_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1928_;
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_of_nat(v___x_1923_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1918_, v_params_1920_, v___x_1929_, v___x_1930_, v___x_1926_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec_ref(v_params_1920_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref_known(v___x_1931_, 1);
v___x_1932_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1917_, v___x_1919_, v_code_1921_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1932_;
}
else
{
lean_dec_ref(v_code_1921_);
lean_dec_ref(v___x_1919_);
return v___x_1931_;
}
}
}
else
{
size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = lean_usize_of_nat(v___x_1923_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1918_, v_params_1920_, v___x_1933_, v___x_1934_, v___x_1926_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec_ref(v_params_1920_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref_known(v___x_1935_, 1);
v___x_1936_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1917_, v___x_1919_, v_code_1921_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1936_;
}
else
{
lean_dec_ref(v_code_1921_);
lean_dec_ref(v___x_1919_);
return v___x_1935_;
}
}
}
}
case 1:
{
lean_object* v_code_1937_; lean_object* v___x_1938_; 
lean_dec(v___x_1918_);
v_code_1937_ = lean_ctor_get(v_alt_1909_, 1);
lean_inc_ref(v_code_1937_);
lean_dec_ref_known(v_alt_1909_, 2);
v___x_1938_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1917_, v___x_1919_, v_code_1937_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1938_;
}
default: 
{
lean_object* v_code_1939_; lean_object* v___x_1940_; 
lean_dec(v___x_1918_);
v_code_1939_ = lean_ctor_get(v_alt_1909_, 0);
lean_inc_ref(v_code_1939_);
lean_dec_ref_known(v_alt_1909_, 1);
v___x_1940_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1917_, v___x_1919_, v_code_1939_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec(v_a_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1950_, lean_object* v_f_1951_, lean_object* v_param_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1951_, v_param_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1961_, lean_object* v_f_1962_, lean_object* v_param_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
uint8_t v_pu_boxed_1971_; lean_object* v_res_1972_; 
v_pu_boxed_1971_ = lean_unbox(v_pu_1961_);
v_res_1972_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1971_, v_f_1962_, v_param_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1973_, lean_object* v_alt_1974_, lean_object* v_f_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1974_, v_f_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1984_, lean_object* v_alt_1985_, lean_object* v_f_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v_pu_boxed_1994_; lean_object* v_res_1995_; 
v_pu_boxed_1994_ = lean_unbox(v_pu_1984_);
v_res_1995_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1994_, v_alt_1985_, v_f_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec(v___y_1987_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1996_, lean_object* v_f_1997_, lean_object* v_arg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1997_, v_arg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_2007_, lean_object* v_f_2008_, lean_object* v_arg_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v_pu_boxed_2017_; lean_object* v_res_2018_; 
v_pu_boxed_2017_ = lean_unbox(v_pu_2007_);
v_res_2018_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_2017_, v_f_2008_, v_arg_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_2019_, size_t v_i_2020_, size_t v_stop_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v___x_2030_; 
v___x_2030_ = lean_usize_dec_eq(v_i_2020_, v_stop_2021_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_array_uget_borrowed(v_as_2019_, v_i_2020_);
lean_inc(v___x_2031_);
v___x_2032_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_2031_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; size_t v___x_2034_; size_t v___x_2035_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_add(v_i_2020_, v___x_2034_);
v_i_2020_ = v___x_2035_;
v_b_2022_ = v_a_2033_;
goto _start;
}
else
{
return v___x_2032_;
}
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_b_2022_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_2038_, lean_object* v_i_2039_, lean_object* v_stop_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
size_t v_i_boxed_2049_; size_t v_stop_boxed_2050_; lean_object* v_res_2051_; 
v_i_boxed_2049_ = lean_unbox_usize(v_i_2039_);
lean_dec(v_i_2039_);
v_stop_boxed_2050_ = lean_unbox_usize(v_stop_2040_);
lean_dec(v_stop_2040_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_2038_, v_i_boxed_2049_, v_stop_boxed_2050_, v_b_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v_as_2038_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_alts_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_alts_2060_ = lean_ctor_get(v_cs_2052_, 3);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_array_get_size(v_alts_2060_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
return v___x_2065_;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_nat_dec_le(v___x_2062_, v___x_2062_);
if (v___x_2066_ == 0)
{
if (v___x_2064_ == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2063_);
return v___x_2067_;
}
else
{
size_t v___x_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = ((size_t)0ULL);
v___x_2069_ = lean_usize_of_nat(v___x_2062_);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_2060_, v___x_2068_, v___x_2069_, v___x_2063_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
return v___x_2070_;
}
}
else
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_of_nat(v___x_2062_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_2060_, v___x_2071_, v___x_2072_, v___x_2063_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_cs_2074_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
if (lean_obj_tag(v_x_2084_) == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_x_2083_);
return v___x_2090_;
}
else
{
lean_object* v_head_2091_; lean_object* v_tail_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2373_; 
v_head_2091_ = lean_ctor_get(v_x_2084_, 0);
v_tail_2092_ = lean_ctor_get(v_x_2084_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2084_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2094_ = v_x_2084_;
v_isShared_2095_ = v_isSharedCheck_2373_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_tail_2092_);
lean_inc(v_head_2091_);
lean_dec(v_x_2084_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2373_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v_i_2108_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v_i_2131_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v_i_2146_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v_i_2169_; lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2372_; 
v_fst_2174_ = lean_ctor_get(v_x_2083_, 0);
v_snd_2175_ = lean_ctor_get(v_x_2083_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_x_2083_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2177_ = v_x_2083_;
v_isShared_2178_ = v_isSharedCheck_2372_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_inc(v_fst_2174_);
lean_dec(v_x_2083_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2372_;
goto v_resetjp_2176_;
}
v___jp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 0);
lean_ctor_set(v___x_2094_, 1, v___y_2097_);
lean_ctor_set(v___x_2094_, 0, v___y_2098_);
v___x_2100_ = v___x_2094_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___y_2098_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___y_2097_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
v_x_2083_ = v___x_2100_;
v_x_2084_ = v_tail_2092_;
goto _start;
}
}
v___jp_2103_:
{
lean_object* v_size_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_size_2109_ = lean_ctor_get(v___y_2104_, 0);
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = lean_nat_add(v_size_2109_, v___x_2110_);
v___x_2112_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2104_, v___x_2111_, v_i_2108_, v___y_2105_, v___y_2107_);
lean_dec(v_i_2108_);
v___y_2097_ = v___y_2106_;
v___y_2098_ = v___x_2112_;
goto v___jp_2096_;
}
v___jp_2113_:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_2117_, v___y_2114_);
switch(lean_obj_tag(v___x_2118_))
{
case 0:
{
lean_object* v_index_2119_; lean_object* v_size_2120_; lean_object* v___x_2121_; 
v_index_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_index_2119_);
lean_dec_ref_known(v___x_2118_, 3);
v_size_2120_ = lean_ctor_get(v___y_2117_, 0);
lean_inc(v_size_2120_);
v___x_2121_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2117_, v_size_2120_, v_index_2119_, v___y_2114_, v___y_2116_);
lean_dec(v_index_2119_);
v___y_2097_ = v___y_2115_;
v___y_2098_ = v___x_2121_;
goto v___jp_2096_;
}
case 1:
{
lean_object* v_index_2122_; 
v_index_2122_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_index_2122_);
lean_dec_ref_known(v___x_2118_, 1);
v___y_2104_ = v___y_2117_;
v___y_2105_ = v___y_2114_;
v___y_2106_ = v___y_2115_;
v___y_2107_ = v___y_2116_;
v_i_2108_ = v_index_2122_;
goto v___jp_2103_;
}
default: 
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2117_, v___x_2123_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_index_2125_; 
v_index_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_index_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___y_2104_ = v___y_2117_;
v___y_2105_ = v___y_2114_;
v___y_2106_ = v___y_2115_;
v___y_2107_ = v___y_2116_;
v_i_2108_ = v_index_2125_;
goto v___jp_2103_;
}
else
{
lean_dec(v___y_2116_);
lean_dec(v___y_2114_);
v___y_2097_ = v___y_2115_;
v___y_2098_ = v___y_2117_;
goto v___jp_2096_;
}
}
}
}
v___jp_2126_:
{
lean_object* v_size_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_size_2132_ = lean_ctor_get(v___y_2128_, 0);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_add(v_size_2132_, v___x_2133_);
v___x_2135_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2128_, v___x_2134_, v_i_2131_, v___y_2127_, v___y_2130_);
lean_dec(v_i_2131_);
v___y_2097_ = v___y_2129_;
v___y_2098_ = v___x_2135_;
goto v___jp_2096_;
}
v___jp_2136_:
{
lean_object* v___x_2139_; 
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___y_2138_);
lean_ctor_set(v___x_2139_, 1, v___y_2137_);
v_x_2083_ = v___x_2139_;
v_x_2084_ = v_tail_2092_;
goto _start;
}
v___jp_2141_:
{
lean_object* v_size_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_size_2147_ = lean_ctor_get(v___y_2144_, 0);
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = lean_nat_add(v_size_2147_, v___x_2148_);
v___x_2150_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2144_, v___x_2149_, v_i_2146_, v___y_2143_, v___y_2142_);
lean_dec(v_i_2146_);
v___y_2137_ = v___y_2145_;
v___y_2138_ = v___x_2150_;
goto v___jp_2136_;
}
v___jp_2151_:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_2155_, v___y_2153_);
switch(lean_obj_tag(v___x_2156_))
{
case 0:
{
lean_object* v_index_2157_; lean_object* v_size_2158_; lean_object* v___x_2159_; 
v_index_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_index_2157_);
lean_dec_ref_known(v___x_2156_, 3);
v_size_2158_ = lean_ctor_get(v___y_2155_, 0);
lean_inc(v_size_2158_);
v___x_2159_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2155_, v_size_2158_, v_index_2157_, v___y_2153_, v___y_2152_);
lean_dec(v_index_2157_);
v___y_2137_ = v___y_2154_;
v___y_2138_ = v___x_2159_;
goto v___jp_2136_;
}
case 1:
{
lean_object* v_index_2160_; 
v_index_2160_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_index_2160_);
lean_dec_ref_known(v___x_2156_, 1);
v___y_2142_ = v___y_2152_;
v___y_2143_ = v___y_2153_;
v___y_2144_ = v___y_2155_;
v___y_2145_ = v___y_2154_;
v_i_2146_ = v_index_2160_;
goto v___jp_2141_;
}
default: 
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2155_, v___x_2161_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_index_2163_; 
v_index_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_index_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___y_2142_ = v___y_2152_;
v___y_2143_ = v___y_2153_;
v___y_2144_ = v___y_2155_;
v___y_2145_ = v___y_2154_;
v_i_2146_ = v_index_2163_;
goto v___jp_2141_;
}
else
{
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
v___y_2137_ = v___y_2154_;
v___y_2138_ = v___y_2155_;
goto v___jp_2136_;
}
}
}
}
v___jp_2164_:
{
lean_object* v_size_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_size_2170_ = lean_ctor_get(v___y_2165_, 0);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_size_2170_, v___x_2171_);
v___x_2173_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2165_, v___x_2172_, v_i_2169_, v___y_2167_, v___y_2166_);
lean_dec(v_i_2169_);
v___y_2137_ = v___y_2168_;
v___y_2138_ = v___x_2173_;
goto v___jp_2136_;
}
v_resetjp_2176_:
{
lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; 
if (lean_obj_tag(v_head_2091_) == 0)
{
lean_object* v_decl_2288_; lean_object* v___x_2289_; 
v_decl_2288_ = lean_ctor_get(v_head_2091_, 0);
lean_inc_ref(v_decl_2288_);
v___x_2289_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_2288_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___y_2292_; uint8_t v___x_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2297_ = lean_unbox(v_a_2290_);
lean_dec(v_a_2290_);
if (v___x_2297_ == 0)
{
lean_del_object(v___x_2177_);
v___y_2206_ = v___y_2085_;
v___y_2207_ = v___y_2086_;
v___y_2208_ = v___y_2087_;
v___y_2209_ = v___y_2088_;
goto v___jp_2205_;
}
else
{
lean_object* v_fvarId_2298_; lean_object* v___x_2299_; lean_object* v___y_2301_; lean_object* v_i_2302_; lean_object* v___y_2308_; lean_object* v___y_2318_; lean_object* v_i_2319_; lean_object* v___x_2334_; 
lean_inc_ref(v_decl_2288_);
lean_dec_ref_known(v_head_2091_, 1);
lean_del_object(v___x_2094_);
v_fvarId_2298_ = lean_ctor_get(v_decl_2288_, 0);
lean_inc(v_fvarId_2298_);
lean_dec_ref(v_decl_2288_);
v___x_2299_ = lean_box(2);
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_fst_2174_, v_fvarId_2298_);
switch(lean_obj_tag(v___x_2334_))
{
case 0:
{
lean_object* v_index_2335_; lean_object* v_size_2336_; lean_object* v___x_2337_; 
v_index_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_index_2335_);
lean_dec_ref_known(v___x_2334_, 3);
v_size_2336_ = lean_ctor_get(v_fst_2174_, 0);
lean_inc(v_size_2336_);
v___x_2337_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2174_, v_size_2336_, v_index_2335_, v_fvarId_2298_, v___x_2299_);
lean_dec(v_index_2335_);
v___y_2292_ = v___x_2337_;
goto v___jp_2291_;
}
case 1:
{
lean_object* v_index_2338_; lean_object* v_size_2339_; lean_object* v_keyArray_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_index_2338_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_index_2338_);
lean_dec_ref_known(v___x_2334_, 1);
v_size_2339_ = lean_ctor_get(v_fst_2174_, 0);
v_keyArray_2340_ = lean_ctor_get(v_fst_2174_, 1);
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = lean_nat_add(v_size_2339_, v___x_2341_);
v___x_2343_ = lean_array_get_size(v_keyArray_2340_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec(v___x_2342_);
lean_dec(v_index_2338_);
goto v___jp_2324_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2345_ = lean_unsigned_to_nat(4u);
v___x_2346_ = lean_nat_mul(v___x_2342_, v___x_2345_);
v___x_2347_ = lean_unsigned_to_nat(3u);
v___x_2348_ = lean_nat_mul(v___x_2343_, v___x_2347_);
v___x_2349_ = lean_nat_dec_le(v___x_2346_, v___x_2348_);
lean_dec(v___x_2348_);
lean_dec(v___x_2346_);
if (v___x_2349_ == 0)
{
lean_dec(v___x_2342_);
lean_dec(v_index_2338_);
goto v___jp_2324_;
}
else
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2174_, v___x_2342_, v_index_2338_, v_fvarId_2298_, v___x_2299_);
lean_dec(v_index_2338_);
v___y_2292_ = v___x_2350_;
goto v___jp_2291_;
}
}
}
default: 
{
lean_object* v_size_2351_; lean_object* v_keyArray_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_size_2351_ = lean_ctor_get(v_fst_2174_, 0);
v_keyArray_2352_ = lean_ctor_get(v_fst_2174_, 1);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_add(v_size_2351_, v___x_2353_);
v___x_2355_ = lean_array_get_size(v_keyArray_2352_);
v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec(v___x_2354_);
v___x_2357_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2308_ = v___x_2357_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2358_ = lean_unsigned_to_nat(4u);
v___x_2359_ = lean_nat_mul(v___x_2354_, v___x_2358_);
lean_dec(v___x_2354_);
v___x_2360_ = lean_unsigned_to_nat(3u);
v___x_2361_ = lean_nat_mul(v___x_2355_, v___x_2360_);
v___x_2362_ = lean_nat_dec_le(v___x_2359_, v___x_2361_);
lean_dec(v___x_2361_);
lean_dec(v___x_2359_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2308_ = v___x_2363_;
goto v___jp_2307_;
}
else
{
v___y_2308_ = v_fst_2174_;
goto v___jp_2307_;
}
}
}
}
v___jp_2300_:
{
lean_object* v_size_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_size_2303_ = lean_ctor_get(v___y_2301_, 0);
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = lean_nat_add(v_size_2303_, v___x_2304_);
v___x_2306_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2301_, v___x_2305_, v_i_2302_, v_fvarId_2298_, v___x_2299_);
lean_dec(v_i_2302_);
v___y_2292_ = v___x_2306_;
goto v___jp_2291_;
}
v___jp_2307_:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_2308_, v_fvarId_2298_);
switch(lean_obj_tag(v___x_2309_))
{
case 0:
{
lean_object* v_index_2310_; lean_object* v_size_2311_; lean_object* v___x_2312_; 
v_index_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_index_2310_);
lean_dec_ref_known(v___x_2309_, 3);
v_size_2311_ = lean_ctor_get(v___y_2308_, 0);
lean_inc(v_size_2311_);
v___x_2312_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2308_, v_size_2311_, v_index_2310_, v_fvarId_2298_, v___x_2299_);
lean_dec(v_index_2310_);
v___y_2292_ = v___x_2312_;
goto v___jp_2291_;
}
case 1:
{
lean_object* v_index_2313_; 
v_index_2313_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_index_2313_);
lean_dec_ref_known(v___x_2309_, 1);
v___y_2301_ = v___y_2308_;
v_i_2302_ = v_index_2313_;
goto v___jp_2300_;
}
default: 
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2308_, v___x_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_index_2316_; 
v_index_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_index_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___y_2301_ = v___y_2308_;
v_i_2302_ = v_index_2316_;
goto v___jp_2300_;
}
else
{
lean_dec(v_fvarId_2298_);
v___y_2292_ = v___y_2308_;
goto v___jp_2291_;
}
}
}
}
v___jp_2317_:
{
lean_object* v_size_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_size_2320_ = lean_ctor_get(v___y_2318_, 0);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v_size_2320_, v___x_2321_);
v___x_2323_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2318_, v___x_2322_, v_i_2319_, v_fvarId_2298_, v___x_2299_);
lean_dec(v_i_2319_);
v___y_2292_ = v___x_2323_;
goto v___jp_2291_;
}
v___jp_2324_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___x_2326_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_2325_, v_fvarId_2298_);
switch(lean_obj_tag(v___x_2326_))
{
case 0:
{
lean_object* v_index_2327_; lean_object* v_size_2328_; lean_object* v___x_2329_; 
v_index_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_index_2327_);
lean_dec_ref_known(v___x_2326_, 3);
v_size_2328_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_size_2328_);
v___x_2329_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2325_, v_size_2328_, v_index_2327_, v_fvarId_2298_, v___x_2299_);
lean_dec(v_index_2327_);
v___y_2292_ = v___x_2329_;
goto v___jp_2291_;
}
case 1:
{
lean_object* v_index_2330_; 
v_index_2330_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_index_2330_);
lean_dec_ref_known(v___x_2326_, 1);
v___y_2318_ = v___x_2325_;
v_i_2319_ = v_index_2330_;
goto v___jp_2317_;
}
default: 
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2325_, v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_index_2333_; 
v_index_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_index_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___y_2318_ = v___x_2325_;
v_i_2319_ = v_index_2333_;
goto v___jp_2317_;
}
else
{
lean_dec(v_fvarId_2298_);
v___y_2292_ = v___x_2325_;
goto v___jp_2291_;
}
}
}
}
}
v___jp_2291_:
{
lean_object* v___x_2294_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___y_2292_);
v___x_2294_ = v___x_2177_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___y_2292_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_snd_2175_);
v___x_2294_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
v_x_2083_ = v___x_2294_;
v_x_2084_ = v_tail_2092_;
goto _start;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref_known(v_head_2091_, 1);
lean_del_object(v___x_2177_);
lean_dec(v_snd_2175_);
lean_dec(v_fst_2174_);
lean_del_object(v___x_2094_);
lean_dec(v_tail_2092_);
v_a_2364_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2289_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2289_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_del_object(v___x_2177_);
v___y_2206_ = v___y_2085_;
v___y_2207_ = v___y_2086_;
v___y_2208_ = v___y_2087_;
v___y_2209_ = v___y_2088_;
goto v___jp_2205_;
}
v___jp_2179_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___x_2184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_2183_, v___y_2181_);
switch(lean_obj_tag(v___x_2184_))
{
case 0:
{
lean_object* v_index_2185_; lean_object* v_size_2186_; lean_object* v___x_2187_; 
v_index_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_index_2185_);
lean_dec_ref_known(v___x_2184_, 3);
v_size_2186_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_size_2186_);
v___x_2187_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2183_, v_size_2186_, v_index_2185_, v___y_2181_, v___y_2180_);
lean_dec(v_index_2185_);
v___y_2137_ = v___y_2182_;
v___y_2138_ = v___x_2187_;
goto v___jp_2136_;
}
case 1:
{
lean_object* v_index_2188_; 
v_index_2188_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_index_2188_);
lean_dec_ref_known(v___x_2184_, 1);
v___y_2165_ = v___x_2183_;
v___y_2166_ = v___y_2180_;
v___y_2167_ = v___y_2181_;
v___y_2168_ = v___y_2182_;
v_i_2169_ = v_index_2188_;
goto v___jp_2164_;
}
default: 
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2183_, v___x_2189_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_index_2191_; 
v_index_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_index_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___y_2165_ = v___x_2183_;
v___y_2166_ = v___y_2180_;
v___y_2167_ = v___y_2181_;
v___y_2168_ = v___y_2182_;
v_i_2169_ = v_index_2191_;
goto v___jp_2164_;
}
else
{
lean_dec(v___y_2181_);
lean_dec(v___y_2180_);
v___y_2137_ = v___y_2182_;
v___y_2138_ = v___x_2183_;
goto v___jp_2136_;
}
}
}
}
v___jp_2192_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___x_2197_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_2196_, v___y_2193_);
switch(lean_obj_tag(v___x_2197_))
{
case 0:
{
lean_object* v_index_2198_; lean_object* v_size_2199_; lean_object* v___x_2200_; 
v_index_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_index_2198_);
lean_dec_ref_known(v___x_2197_, 3);
v_size_2199_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_size_2199_);
v___x_2200_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2196_, v_size_2199_, v_index_2198_, v___y_2193_, v___y_2195_);
lean_dec(v_index_2198_);
v___y_2097_ = v___y_2194_;
v___y_2098_ = v___x_2200_;
goto v___jp_2096_;
}
case 1:
{
lean_object* v_index_2201_; 
v_index_2201_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_index_2201_);
lean_dec_ref_known(v___x_2197_, 1);
v___y_2127_ = v___y_2193_;
v___y_2128_ = v___x_2196_;
v___y_2129_ = v___y_2194_;
v___y_2130_ = v___y_2195_;
v_i_2131_ = v_index_2201_;
goto v___jp_2126_;
}
default: 
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2196_, v___x_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_index_2204_; 
v_index_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_index_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___y_2127_ = v___y_2193_;
v___y_2128_ = v___x_2196_;
v___y_2129_ = v___y_2194_;
v___y_2130_ = v___y_2195_;
v_i_2131_ = v_index_2204_;
goto v___jp_2126_;
}
else
{
lean_dec(v___y_2195_);
lean_dec(v___y_2193_);
v___y_2097_ = v___y_2194_;
v___y_2098_ = v___x_2196_;
goto v___jp_2096_;
}
}
}
}
v___jp_2205_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_st_ref_get(v___y_2209_);
lean_dec(v___x_2210_);
v___x_2211_ = lean_st_mk_ref(v_snd_2175_);
lean_inc(v_head_2091_);
v___x_2212_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_2091_, v___x_2211_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = lean_st_ref_get(v___x_2211_);
lean_dec(v___x_2211_);
v___x_2215_ = lean_unbox(v_a_2213_);
lean_dec(v_a_2213_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_del_object(v___x_2094_);
v___x_2216_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_2091_);
lean_dec(v_head_2091_);
v___x_2217_ = lean_box(3);
v___x_2218_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_fst_2174_, v___x_2216_);
switch(lean_obj_tag(v___x_2218_))
{
case 0:
{
lean_object* v_index_2219_; lean_object* v_size_2220_; lean_object* v___x_2221_; 
v_index_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_index_2219_);
lean_dec_ref_known(v___x_2218_, 3);
v_size_2220_ = lean_ctor_get(v_fst_2174_, 0);
lean_inc(v_size_2220_);
v___x_2221_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2174_, v_size_2220_, v_index_2219_, v___x_2216_, v___x_2217_);
lean_dec(v_index_2219_);
v___y_2137_ = v___x_2214_;
v___y_2138_ = v___x_2221_;
goto v___jp_2136_;
}
case 1:
{
lean_object* v_index_2222_; lean_object* v_size_2223_; lean_object* v_keyArray_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_index_2222_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_index_2222_);
lean_dec_ref_known(v___x_2218_, 1);
v_size_2223_ = lean_ctor_get(v_fst_2174_, 0);
v_keyArray_2224_ = lean_ctor_get(v_fst_2174_, 1);
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_nat_add(v_size_2223_, v___x_2225_);
v___x_2227_ = lean_array_get_size(v_keyArray_2224_);
v___x_2228_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec(v___x_2226_);
lean_dec(v_index_2222_);
v___y_2180_ = v___x_2217_;
v___y_2181_ = v___x_2216_;
v___y_2182_ = v___x_2214_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2229_ = lean_unsigned_to_nat(4u);
v___x_2230_ = lean_nat_mul(v___x_2226_, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(3u);
v___x_2232_ = lean_nat_mul(v___x_2227_, v___x_2231_);
v___x_2233_ = lean_nat_dec_le(v___x_2230_, v___x_2232_);
lean_dec(v___x_2232_);
lean_dec(v___x_2230_);
if (v___x_2233_ == 0)
{
lean_dec(v___x_2226_);
lean_dec(v_index_2222_);
v___y_2180_ = v___x_2217_;
v___y_2181_ = v___x_2216_;
v___y_2182_ = v___x_2214_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2174_, v___x_2226_, v_index_2222_, v___x_2216_, v___x_2217_);
lean_dec(v_index_2222_);
v___y_2137_ = v___x_2214_;
v___y_2138_ = v___x_2234_;
goto v___jp_2136_;
}
}
}
default: 
{
lean_object* v_size_2235_; lean_object* v_keyArray_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_size_2235_ = lean_ctor_get(v_fst_2174_, 0);
v_keyArray_2236_ = lean_ctor_get(v_fst_2174_, 1);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_size_2235_, v___x_2237_);
v___x_2239_ = lean_array_get_size(v_keyArray_2236_);
v___x_2240_ = lean_nat_dec_lt(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_dec(v___x_2238_);
v___x_2241_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2152_ = v___x_2217_;
v___y_2153_ = v___x_2216_;
v___y_2154_ = v___x_2214_;
v___y_2155_ = v___x_2241_;
goto v___jp_2151_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2242_ = lean_unsigned_to_nat(4u);
v___x_2243_ = lean_nat_mul(v___x_2238_, v___x_2242_);
lean_dec(v___x_2238_);
v___x_2244_ = lean_unsigned_to_nat(3u);
v___x_2245_ = lean_nat_mul(v___x_2239_, v___x_2244_);
v___x_2246_ = lean_nat_dec_le(v___x_2243_, v___x_2245_);
lean_dec(v___x_2245_);
lean_dec(v___x_2243_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2152_ = v___x_2217_;
v___y_2153_ = v___x_2216_;
v___y_2154_ = v___x_2214_;
v___y_2155_ = v___x_2247_;
goto v___jp_2151_;
}
else
{
v___y_2152_ = v___x_2217_;
v___y_2153_ = v___x_2216_;
v___y_2154_ = v___x_2214_;
v___y_2155_ = v_fst_2174_;
goto v___jp_2151_;
}
}
}
}
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_2091_);
lean_dec(v_head_2091_);
v___x_2249_ = lean_box(2);
v___x_2250_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_fst_2174_, v___x_2248_);
switch(lean_obj_tag(v___x_2250_))
{
case 0:
{
lean_object* v_index_2251_; lean_object* v_size_2252_; lean_object* v___x_2253_; 
v_index_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_index_2251_);
lean_dec_ref_known(v___x_2250_, 3);
v_size_2252_ = lean_ctor_get(v_fst_2174_, 0);
lean_inc(v_size_2252_);
v___x_2253_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2174_, v_size_2252_, v_index_2251_, v___x_2248_, v___x_2249_);
lean_dec(v_index_2251_);
v___y_2097_ = v___x_2214_;
v___y_2098_ = v___x_2253_;
goto v___jp_2096_;
}
case 1:
{
lean_object* v_index_2254_; lean_object* v_size_2255_; lean_object* v_keyArray_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_index_2254_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_index_2254_);
lean_dec_ref_known(v___x_2250_, 1);
v_size_2255_ = lean_ctor_get(v_fst_2174_, 0);
v_keyArray_2256_ = lean_ctor_get(v_fst_2174_, 1);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_add(v_size_2255_, v___x_2257_);
v___x_2259_ = lean_array_get_size(v_keyArray_2256_);
v___x_2260_ = lean_nat_dec_lt(v___x_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_dec(v___x_2258_);
lean_dec(v_index_2254_);
v___y_2193_ = v___x_2248_;
v___y_2194_ = v___x_2214_;
v___y_2195_ = v___x_2249_;
goto v___jp_2192_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2261_ = lean_unsigned_to_nat(4u);
v___x_2262_ = lean_nat_mul(v___x_2258_, v___x_2261_);
v___x_2263_ = lean_unsigned_to_nat(3u);
v___x_2264_ = lean_nat_mul(v___x_2259_, v___x_2263_);
v___x_2265_ = lean_nat_dec_le(v___x_2262_, v___x_2264_);
lean_dec(v___x_2264_);
lean_dec(v___x_2262_);
if (v___x_2265_ == 0)
{
lean_dec(v___x_2258_);
lean_dec(v_index_2254_);
v___y_2193_ = v___x_2248_;
v___y_2194_ = v___x_2214_;
v___y_2195_ = v___x_2249_;
goto v___jp_2192_;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2174_, v___x_2258_, v_index_2254_, v___x_2248_, v___x_2249_);
lean_dec(v_index_2254_);
v___y_2097_ = v___x_2214_;
v___y_2098_ = v___x_2266_;
goto v___jp_2096_;
}
}
}
default: 
{
lean_object* v_size_2267_; lean_object* v_keyArray_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_size_2267_ = lean_ctor_get(v_fst_2174_, 0);
v_keyArray_2268_ = lean_ctor_get(v_fst_2174_, 1);
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_add(v_size_2267_, v___x_2269_);
v___x_2271_ = lean_array_get_size(v_keyArray_2268_);
v___x_2272_ = lean_nat_dec_lt(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v___x_2270_);
v___x_2273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2114_ = v___x_2248_;
v___y_2115_ = v___x_2214_;
v___y_2116_ = v___x_2249_;
v___y_2117_ = v___x_2273_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2274_ = lean_unsigned_to_nat(4u);
v___x_2275_ = lean_nat_mul(v___x_2270_, v___x_2274_);
lean_dec(v___x_2270_);
v___x_2276_ = lean_unsigned_to_nat(3u);
v___x_2277_ = lean_nat_mul(v___x_2271_, v___x_2276_);
v___x_2278_ = lean_nat_dec_le(v___x_2275_, v___x_2277_);
lean_dec(v___x_2277_);
lean_dec(v___x_2275_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2114_ = v___x_2248_;
v___y_2115_ = v___x_2214_;
v___y_2116_ = v___x_2249_;
v___y_2117_ = v___x_2279_;
goto v___jp_2113_;
}
else
{
v___y_2114_ = v___x_2248_;
v___y_2115_ = v___x_2214_;
v___y_2116_ = v___x_2249_;
v___y_2117_ = v_fst_2174_;
goto v___jp_2113_;
}
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v___x_2211_);
lean_dec(v_fst_2174_);
lean_del_object(v___x_2094_);
lean_dec(v_tail_2092_);
lean_dec(v_head_2091_);
v_a_2280_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2212_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2212_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2374_, v_x_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2381_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v_cellCount_2382_; lean_object* v___x_2383_; 
v_cellCount_2382_ = lean_unsigned_to_nat(16u);
v___x_2383_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v_cellCount_2384_; lean_object* v___x_2385_; 
v_cellCount_2384_ = lean_unsigned_to_nat(16u);
v___x_2385_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2386_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2387_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
lean_ctor_set(v___x_2389_, 2, v___x_2386_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_map_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_cellCount_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2423_ = l_List_lengthTR___redArg(v_a_2391_);
v___x_2424_ = lean_unsigned_to_nat(4u);
v___x_2425_ = lean_nat_mul(v___x_2423_, v___x_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_unsigned_to_nat(2u);
v___x_2427_ = lean_nat_add(v___x_2425_, v___x_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_unsigned_to_nat(3u);
v___x_2429_ = lean_nat_div(v___x_2427_, v___x_2428_);
lean_dec(v___x_2427_);
v_cellCount_2430_ = l_Nat_nextPowerOfTwo(v___x_2429_);
lean_dec(v___x_2429_);
v___x_2431_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2430_);
v___x_2432_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2430_);
v___x_2433_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2430_);
v___x_2434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2431_);
lean_ctor_set(v___x_2434_, 1, v___x_2432_);
lean_ctor_set(v___x_2434_, 2, v___x_2433_);
v___x_2435_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
lean_inc(v_a_2391_);
v___x_2437_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2436_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v_fst_2439_; lean_object* v_discr_2440_; uint8_t v___x_2441_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v_fst_2439_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_fst_2439_);
lean_dec(v_a_2438_);
v_discr_2440_ = lean_ctor_get(v_cs_2390_, 2);
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2439_, v_discr_2440_);
if (v___x_2441_ == 0)
{
v_map_2398_ = v_fst_2439_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2442_; lean_object* v___y_2444_; lean_object* v_i_2445_; lean_object* v___y_2451_; lean_object* v___y_2460_; lean_object* v_i_2461_; lean_object* v___x_2475_; 
v___x_2442_ = lean_box(2);
v___x_2475_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_fst_2439_, v_discr_2440_);
switch(lean_obj_tag(v___x_2475_))
{
case 0:
{
lean_object* v_index_2476_; lean_object* v_size_2477_; lean_object* v___x_2478_; 
v_index_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_index_2476_);
lean_dec_ref_known(v___x_2475_, 3);
v_size_2477_ = lean_ctor_get(v_fst_2439_, 0);
lean_inc(v_size_2477_);
lean_inc(v_discr_2440_);
v___x_2478_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2439_, v_size_2477_, v_index_2476_, v_discr_2440_, v___x_2442_);
lean_dec(v_index_2476_);
v_map_2398_ = v___x_2478_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
case 1:
{
lean_object* v_index_2479_; lean_object* v_size_2480_; lean_object* v_keyArray_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v_index_2479_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_index_2479_);
lean_dec_ref_known(v___x_2475_, 1);
v_size_2480_ = lean_ctor_get(v_fst_2439_, 0);
v_keyArray_2481_ = lean_ctor_get(v_fst_2439_, 1);
v___x_2482_ = lean_unsigned_to_nat(1u);
v___x_2483_ = lean_nat_add(v_size_2480_, v___x_2482_);
v___x_2484_ = lean_array_get_size(v_keyArray_2481_);
v___x_2485_ = lean_nat_dec_lt(v___x_2483_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_dec(v___x_2483_);
lean_dec(v_index_2479_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2486_ = lean_nat_mul(v___x_2483_, v___x_2424_);
v___x_2487_ = lean_nat_mul(v___x_2484_, v___x_2428_);
v___x_2488_ = lean_nat_dec_le(v___x_2486_, v___x_2487_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
if (v___x_2488_ == 0)
{
lean_dec(v___x_2483_);
lean_dec(v_index_2479_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2489_; 
lean_inc(v_discr_2440_);
v___x_2489_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2439_, v___x_2483_, v_index_2479_, v_discr_2440_, v___x_2442_);
lean_dec(v_index_2479_);
v_map_2398_ = v___x_2489_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
}
}
default: 
{
lean_object* v_size_2490_; lean_object* v_keyArray_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v_size_2490_ = lean_ctor_get(v_fst_2439_, 0);
v_keyArray_2491_ = lean_ctor_get(v_fst_2439_, 1);
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_nat_add(v_size_2490_, v___x_2492_);
v___x_2494_ = lean_array_get_size(v_keyArray_2491_);
v___x_2495_ = lean_nat_dec_lt(v___x_2493_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
lean_dec(v___x_2493_);
v___x_2496_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2439_);
lean_dec(v_fst_2439_);
v___y_2451_ = v___x_2496_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2497_ = lean_nat_mul(v___x_2493_, v___x_2424_);
lean_dec(v___x_2493_);
v___x_2498_ = lean_nat_mul(v___x_2494_, v___x_2428_);
v___x_2499_ = lean_nat_dec_le(v___x_2497_, v___x_2498_);
lean_dec(v___x_2498_);
lean_dec(v___x_2497_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2439_);
lean_dec(v_fst_2439_);
v___y_2451_ = v___x_2500_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v_fst_2439_;
goto v___jp_2450_;
}
}
}
}
v___jp_2443_:
{
lean_object* v_size_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_size_2446_ = lean_ctor_get(v___y_2444_, 0);
v___x_2447_ = lean_unsigned_to_nat(1u);
v___x_2448_ = lean_nat_add(v_size_2446_, v___x_2447_);
lean_inc(v_discr_2440_);
v___x_2449_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2444_, v___x_2448_, v_i_2445_, v_discr_2440_, v___x_2442_);
lean_dec(v_i_2445_);
v_map_2398_ = v___x_2449_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_2451_, v_discr_2440_);
switch(lean_obj_tag(v___x_2452_))
{
case 0:
{
lean_object* v_index_2453_; lean_object* v_size_2454_; lean_object* v___x_2455_; 
v_index_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_index_2453_);
lean_dec_ref_known(v___x_2452_, 3);
v_size_2454_ = lean_ctor_get(v___y_2451_, 0);
lean_inc(v_size_2454_);
lean_inc(v_discr_2440_);
v___x_2455_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2451_, v_size_2454_, v_index_2453_, v_discr_2440_, v___x_2442_);
lean_dec(v_index_2453_);
v_map_2398_ = v___x_2455_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
case 1:
{
lean_object* v_index_2456_; 
v_index_2456_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_index_2456_);
lean_dec_ref_known(v___x_2452_, 1);
v___y_2444_ = v___y_2451_;
v_i_2445_ = v_index_2456_;
goto v___jp_2443_;
}
default: 
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2451_, v___x_2431_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_index_2458_; 
v_index_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_index_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___y_2444_ = v___y_2451_;
v_i_2445_ = v_index_2458_;
goto v___jp_2443_;
}
else
{
v_map_2398_ = v___y_2451_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
}
}
}
v___jp_2459_:
{
lean_object* v_size_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_size_2462_ = lean_ctor_get(v___y_2460_, 0);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_add(v_size_2462_, v___x_2463_);
lean_inc(v_discr_2440_);
v___x_2465_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2460_, v___x_2464_, v_i_2461_, v_discr_2440_, v___x_2442_);
lean_dec(v_i_2461_);
v_map_2398_ = v___x_2465_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
v___jp_2466_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_fst_2439_);
lean_dec(v_fst_2439_);
v___x_2468_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_2467_, v_discr_2440_);
switch(lean_obj_tag(v___x_2468_))
{
case 0:
{
lean_object* v_index_2469_; lean_object* v_size_2470_; lean_object* v___x_2471_; 
v_index_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_index_2469_);
lean_dec_ref_known(v___x_2468_, 3);
v_size_2470_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_size_2470_);
lean_inc(v_discr_2440_);
v___x_2471_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2467_, v_size_2470_, v_index_2469_, v_discr_2440_, v___x_2442_);
lean_dec(v_index_2469_);
v_map_2398_ = v___x_2471_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
case 1:
{
lean_object* v_index_2472_; 
v_index_2472_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_index_2472_);
lean_dec_ref_known(v___x_2468_, 1);
v___y_2460_ = v___x_2467_;
v_i_2461_ = v_index_2472_;
goto v___jp_2459_;
}
default: 
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2467_, v___x_2431_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_index_2474_; 
v_index_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_index_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___y_2460_ = v___x_2467_;
v_i_2461_ = v_index_2474_;
goto v___jp_2459_;
}
else
{
v_map_2398_ = v___x_2467_;
v___y_2399_ = v_a_2391_;
v___y_2400_ = v_a_2392_;
v___y_2401_ = v_a_2393_;
v___y_2402_ = v_a_2394_;
v___y_2403_ = v_a_2395_;
goto v___jp_2397_;
}
}
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v_cs_2390_);
v_a_2501_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2437_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2437_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
v___jp_2397_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_st_mk_ref(v_map_2398_);
v___x_2405_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_2390_, v___x_2404_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec_ref(v_cs_2390_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2413_; 
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v___x_2405_, 0);
lean_dec(v_unused_2414_);
v___x_2407_ = v___x_2405_;
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
else
{
lean_dec(v___x_2405_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_st_ref_get(v___x_2404_);
lean_dec(v___x_2404_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2411_ = v___x_2407_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v___x_2404_);
v_a_2415_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2405_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2405_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2517_, lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2517_, v_x_2518_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2526_, lean_object* v_x_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2526_, v_x_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_m_2535_, lean_object* v_query_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
lean_object* v_zero_2540_; uint8_t v_isZero_2541_; 
v_zero_2540_ = lean_unsigned_to_nat(0u);
v_isZero_2541_ = lean_nat_dec_eq(v_x_2538_, v_zero_2540_);
if (v_isZero_2541_ == 1)
{
lean_dec(v_x_2539_);
lean_dec(v_x_2538_);
if (lean_obj_tag(v_x_2537_) == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_box(2);
return v___x_2542_;
}
else
{
lean_object* v_val_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_val_2543_ = lean_ctor_get(v_x_2537_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2537_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v_x_2537_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_val_2543_);
lean_dec(v_x_2537_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_val_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v_keyArray_2551_; lean_object* v_valueArray_2552_; lean_object* v___x_2553_; uint8_t v_isSome_2554_; 
v_keyArray_2551_ = lean_ctor_get(v_m_2535_, 1);
v_valueArray_2552_ = lean_ctor_get(v_m_2535_, 2);
v___x_2553_ = lean_array_fget_borrowed(v_keyArray_2551_, v_x_2539_);
v_isSome_2554_ = lean_noption_is_some(v___x_2553_);
if (v_isSome_2554_ == 0)
{
lean_dec(v_x_2538_);
if (lean_obj_tag(v_x_2537_) == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_x_2539_);
return v___x_2555_;
}
else
{
lean_object* v_val_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_x_2539_);
v_val_2556_ = lean_ctor_get(v_x_2537_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2537_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v_x_2537_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_val_2556_);
lean_dec(v_x_2537_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_val_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_one_2564_; lean_object* v_n_2565_; lean_object* v___y_2567_; 
v_one_2564_ = lean_unsigned_to_nat(1u);
v_n_2565_ = lean_nat_sub(v_x_2538_, v_one_2564_);
lean_dec(v_x_2538_);
if (v_isSome_2554_ == 0)
{
goto v___jp_2573_;
}
else
{
lean_object* v___x_2575_; uint8_t v_isSome_2576_; 
v___x_2575_ = lean_array_fget_borrowed(v_valueArray_2552_, v_x_2539_);
v_isSome_2576_ = lean_noption_is_some(v___x_2575_);
if (v_isSome_2576_ == 0)
{
goto v___jp_2573_;
}
else
{
lean_object* v_val_2577_; uint8_t v___x_2578_; 
lean_inc(v___x_2553_);
v_val_2577_ = lean_noption_get(v___x_2553_);
v___x_2578_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_2577_, v_query_2536_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
lean_dec(v_val_2577_);
v___x_2579_ = lean_array_get_size(v_keyArray_2551_);
v___x_2580_ = lean_nat_add(v_x_2539_, v_one_2564_);
lean_dec(v_x_2539_);
v___x_2581_ = lean_nat_dec_lt(v___x_2580_, v___x_2579_);
if (v___x_2581_ == 0)
{
lean_dec(v___x_2580_);
v_x_2538_ = v_n_2565_;
v_x_2539_ = v_zero_2540_;
goto _start;
}
else
{
v_x_2538_ = v_n_2565_;
v_x_2539_ = v___x_2580_;
goto _start;
}
}
else
{
lean_object* v_val_2584_; lean_object* v___x_2585_; 
lean_dec(v_n_2565_);
lean_dec(v_x_2537_);
lean_inc(v___x_2575_);
v_val_2584_ = lean_noption_get(v___x_2575_);
v___x_2585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2585_, 0, v_x_2539_);
lean_ctor_set(v___x_2585_, 1, v_val_2577_);
lean_ctor_set(v___x_2585_, 2, v_val_2584_);
return v___x_2585_;
}
}
}
v___jp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = lean_array_get_size(v_keyArray_2551_);
v___x_2569_ = lean_nat_add(v_x_2539_, v_one_2564_);
lean_dec(v_x_2539_);
v___x_2570_ = lean_nat_dec_lt(v___x_2569_, v___x_2568_);
if (v___x_2570_ == 0)
{
lean_dec(v___x_2569_);
v_x_2537_ = v___y_2567_;
v_x_2538_ = v_n_2565_;
v_x_2539_ = v_zero_2540_;
goto _start;
}
else
{
v_x_2537_ = v___y_2567_;
v_x_2538_ = v_n_2565_;
v_x_2539_ = v___x_2569_;
goto _start;
}
}
v___jp_2573_:
{
if (lean_obj_tag(v_x_2537_) == 0)
{
lean_object* v___x_2574_; 
lean_inc(v_x_2539_);
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_x_2539_);
v___y_2567_ = v___x_2574_;
goto v___jp_2566_;
}
else
{
v___y_2567_ = v_x_2537_;
goto v___jp_2566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_m_2586_, lean_object* v_query_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_m_2586_, v_query_2587_, v_x_2588_, v_x_2589_, v_x_2590_);
lean_dec(v_query_2587_);
lean_dec_ref(v_m_2586_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2592_, lean_object* v_query_2593_){
_start:
{
lean_object* v_keyArray_2594_; lean_object* v___x_2595_; uint64_t v___x_2596_; uint64_t v___x_2597_; uint64_t v___x_2598_; uint64_t v_fold_2599_; uint64_t v___x_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_keyArray_2594_ = lean_ctor_get(v_m_2592_, 1);
v___x_2595_ = lean_array_get_size(v_keyArray_2594_);
v___x_2596_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_query_2593_);
v___x_2597_ = 32ULL;
v___x_2598_ = lean_uint64_shift_right(v___x_2596_, v___x_2597_);
v_fold_2599_ = lean_uint64_xor(v___x_2596_, v___x_2598_);
v___x_2600_ = 16ULL;
v___x_2601_ = lean_uint64_shift_right(v_fold_2599_, v___x_2600_);
v___x_2602_ = lean_uint64_xor(v_fold_2599_, v___x_2601_);
v___x_2603_ = lean_uint64_to_usize(v___x_2602_);
v___x_2604_ = lean_usize_of_nat(v___x_2595_);
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_sub(v___x_2604_, v___x_2605_);
v___x_2607_ = lean_usize_land(v___x_2603_, v___x_2606_);
v___x_2608_ = lean_usize_to_nat(v___x_2607_);
v___x_2609_ = lean_box(0);
v___x_2610_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_m_2592_, v_query_2593_, v___x_2609_, v___x_2595_, v___x_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg___boxed(lean_object* v_m_2611_, lean_object* v_query_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2611_, v_query_2612_);
lean_dec(v_query_2612_);
lean_dec_ref(v_m_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg(lean_object* v_b_2614_, lean_object* v_acc_2615_, lean_object* v_i_2616_){
_start:
{
lean_object* v___y_2618_; lean_object* v_keyArray_2626_; lean_object* v_valueArray_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_keyArray_2626_ = lean_ctor_get(v_b_2614_, 1);
v_valueArray_2627_ = lean_ctor_get(v_b_2614_, 2);
v___x_2628_ = lean_array_get_size(v_keyArray_2626_);
v___x_2629_ = lean_nat_dec_lt(v_i_2616_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_dec(v_i_2616_);
return v_acc_2615_;
}
else
{
lean_object* v___x_2630_; uint8_t v_isSome_2631_; 
v___x_2630_ = lean_array_fget_borrowed(v_keyArray_2626_, v_i_2616_);
v_isSome_2631_ = lean_noption_is_some(v___x_2630_);
if (v_isSome_2631_ == 0)
{
goto v___jp_2622_;
}
else
{
lean_object* v___x_2632_; uint8_t v_isSome_2633_; 
v___x_2632_ = lean_array_fget_borrowed(v_valueArray_2627_, v_i_2616_);
v_isSome_2633_ = lean_noption_is_some(v___x_2632_);
if (v_isSome_2633_ == 0)
{
goto v___jp_2622_;
}
else
{
lean_object* v_val_2634_; lean_object* v_val_2635_; lean_object* v_i_2637_; lean_object* v___x_2642_; 
lean_inc(v___x_2630_);
v_val_2634_ = lean_noption_get(v___x_2630_);
lean_inc(v___x_2632_);
v_val_2635_ = lean_noption_get(v___x_2632_);
v___x_2642_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_acc_2615_, v_val_2634_);
switch(lean_obj_tag(v___x_2642_))
{
case 0:
{
lean_object* v_index_2643_; lean_object* v_size_2644_; lean_object* v___x_2645_; 
v_index_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_index_2643_);
lean_dec_ref_known(v___x_2642_, 3);
v_size_2644_ = lean_ctor_get(v_acc_2615_, 0);
lean_inc(v_size_2644_);
v___x_2645_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2615_, v_size_2644_, v_index_2643_, v_val_2634_, v_val_2635_);
lean_dec(v_index_2643_);
v___y_2618_ = v___x_2645_;
goto v___jp_2617_;
}
case 1:
{
lean_object* v_index_2646_; 
v_index_2646_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_index_2646_);
lean_dec_ref_known(v___x_2642_, 1);
v_i_2637_ = v_index_2646_;
goto v___jp_2636_;
}
default: 
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2615_, v___x_2647_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_index_2649_; 
v_index_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_index_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v_i_2637_ = v_index_2649_;
goto v___jp_2636_;
}
else
{
lean_dec(v_val_2635_);
lean_dec(v_val_2634_);
v___y_2618_ = v_acc_2615_;
goto v___jp_2617_;
}
}
}
v___jp_2636_:
{
lean_object* v_size_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_size_2638_ = lean_ctor_get(v_acc_2615_, 0);
v___x_2639_ = lean_unsigned_to_nat(1u);
v___x_2640_ = lean_nat_add(v_size_2638_, v___x_2639_);
v___x_2641_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2615_, v___x_2640_, v_i_2637_, v_val_2634_, v_val_2635_);
lean_dec(v_i_2637_);
v___y_2618_ = v___x_2641_;
goto v___jp_2617_;
}
}
}
}
v___jp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_unsigned_to_nat(1u);
v___x_2620_ = lean_nat_add(v_i_2616_, v___x_2619_);
lean_dec(v_i_2616_);
v_acc_2615_ = v___y_2618_;
v_i_2616_ = v___x_2620_;
goto _start;
}
v___jp_2622_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = lean_nat_add(v_i_2616_, v___x_2623_);
lean_dec(v_i_2616_);
v_i_2616_ = v___x_2624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_2650_, lean_object* v_acc_2651_, lean_object* v_i_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg(v_b_2650_, v_acc_2651_, v_i_2652_);
lean_dec_ref(v_b_2650_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg(lean_object* v_init_2654_, lean_object* v_b_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg(v_b_2655_, v_init_2654_, v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg___boxed(lean_object* v_init_2658_, lean_object* v_b_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg(v_init_2658_, v_b_2659_);
lean_dec_ref(v_b_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(lean_object* v_m_2661_){
_start:
{
lean_object* v_keyArray_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v_cellCount_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_target_2669_; lean_object* v___x_2670_; 
v_keyArray_2662_ = lean_ctor_get(v_m_2661_, 1);
v___x_2663_ = lean_array_get_size(v_keyArray_2662_);
v___x_2664_ = lean_unsigned_to_nat(2u);
v_cellCount_2665_ = lean_nat_mul(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2665_);
v___x_2667_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2665_);
v___x_2668_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2665_);
v_target_2669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2669_, 0, v___x_2666_);
lean_ctor_set(v_target_2669_, 1, v___x_2667_);
lean_ctor_set(v_target_2669_, 2, v___x_2668_);
v___x_2670_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg(v_target_2669_, v_m_2661_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg___boxed(lean_object* v_m_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_m_2671_);
lean_dec_ref(v_m_2671_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__2(lean_object* v_as_2673_, size_t v_i_2674_, size_t v_stop_2675_, lean_object* v_b_2676_){
_start:
{
uint8_t v___x_2677_; 
v___x_2677_ = lean_usize_dec_eq(v_i_2674_, v_stop_2675_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___y_2684_; lean_object* v_i_2685_; lean_object* v___y_2692_; lean_object* v___y_2704_; lean_object* v_i_2705_; lean_object* v___x_2723_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_sub(v_i_2674_, v___x_2679_);
v___x_2681_ = lean_array_uget_borrowed(v_as_2673_, v___x_2680_);
v___x_2682_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2681_);
v___x_2723_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2676_, v___x_2682_);
switch(lean_obj_tag(v___x_2723_))
{
case 0:
{
lean_object* v_index_2724_; lean_object* v_size_2725_; lean_object* v___x_2726_; 
v_index_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_index_2724_);
lean_dec_ref_known(v___x_2723_, 3);
v_size_2725_ = lean_ctor_get(v_b_2676_, 0);
lean_inc(v_size_2725_);
v___x_2726_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_2676_, v_size_2725_, v_index_2724_, v___x_2682_, v___x_2678_);
lean_dec(v_index_2724_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2726_;
goto _start;
}
case 1:
{
lean_object* v_index_2728_; lean_object* v_size_2729_; lean_object* v_keyArray_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_index_2728_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_index_2728_);
lean_dec_ref_known(v___x_2723_, 1);
v_size_2729_ = lean_ctor_get(v_b_2676_, 0);
v_keyArray_2730_ = lean_ctor_get(v_b_2676_, 1);
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = lean_nat_add(v_size_2729_, v___x_2731_);
v___x_2733_ = lean_array_get_size(v_keyArray_2730_);
v___x_2734_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_dec(v___x_2732_);
lean_dec(v_index_2728_);
goto v___jp_2711_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2735_ = lean_unsigned_to_nat(4u);
v___x_2736_ = lean_nat_mul(v___x_2732_, v___x_2735_);
v___x_2737_ = lean_unsigned_to_nat(3u);
v___x_2738_ = lean_nat_mul(v___x_2733_, v___x_2737_);
v___x_2739_ = lean_nat_dec_le(v___x_2736_, v___x_2738_);
lean_dec(v___x_2738_);
lean_dec(v___x_2736_);
if (v___x_2739_ == 0)
{
lean_dec(v___x_2732_);
lean_dec(v_index_2728_);
goto v___jp_2711_;
}
else
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_2676_, v___x_2732_, v_index_2728_, v___x_2682_, v___x_2678_);
lean_dec(v_index_2728_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2740_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_2742_; lean_object* v_keyArray_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v_size_2742_ = lean_ctor_get(v_b_2676_, 0);
v_keyArray_2743_ = lean_ctor_get(v_b_2676_, 1);
v___x_2744_ = lean_unsigned_to_nat(1u);
v___x_2745_ = lean_nat_add(v_size_2742_, v___x_2744_);
v___x_2746_ = lean_array_get_size(v_keyArray_2743_);
v___x_2747_ = lean_nat_dec_lt(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; 
lean_dec(v___x_2745_);
v___x_2748_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_b_2676_);
lean_dec_ref(v_b_2676_);
v___y_2692_ = v___x_2748_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2749_ = lean_unsigned_to_nat(4u);
v___x_2750_ = lean_nat_mul(v___x_2745_, v___x_2749_);
lean_dec(v___x_2745_);
v___x_2751_ = lean_unsigned_to_nat(3u);
v___x_2752_ = lean_nat_mul(v___x_2746_, v___x_2751_);
v___x_2753_ = lean_nat_dec_le(v___x_2750_, v___x_2752_);
lean_dec(v___x_2752_);
lean_dec(v___x_2750_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_b_2676_);
lean_dec_ref(v_b_2676_);
v___y_2692_ = v___x_2754_;
goto v___jp_2691_;
}
else
{
v___y_2692_ = v_b_2676_;
goto v___jp_2691_;
}
}
}
}
v___jp_2683_:
{
lean_object* v_size_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_size_2686_ = lean_ctor_get(v___y_2684_, 0);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_size_2686_, v___x_2687_);
v___x_2689_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2684_, v___x_2688_, v_i_2685_, v___x_2682_, v___x_2678_);
lean_dec(v_i_2685_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2689_;
goto _start;
}
v___jp_2691_:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___y_2692_, v___x_2682_);
switch(lean_obj_tag(v___x_2693_))
{
case 0:
{
lean_object* v_index_2694_; lean_object* v_size_2695_; lean_object* v___x_2696_; 
v_index_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_index_2694_);
lean_dec_ref_known(v___x_2693_, 3);
v_size_2695_ = lean_ctor_get(v___y_2692_, 0);
lean_inc(v_size_2695_);
v___x_2696_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2692_, v_size_2695_, v_index_2694_, v___x_2682_, v___x_2678_);
lean_dec(v_index_2694_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2696_;
goto _start;
}
case 1:
{
lean_object* v_index_2698_; 
v_index_2698_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_index_2698_);
lean_dec_ref_known(v___x_2693_, 1);
v___y_2684_ = v___y_2692_;
v_i_2685_ = v_index_2698_;
goto v___jp_2683_;
}
default: 
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2692_, v___x_2699_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_index_2701_; 
v_index_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_index_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___y_2684_ = v___y_2692_;
v_i_2685_ = v_index_2701_;
goto v___jp_2683_;
}
else
{
lean_dec(v___x_2682_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___y_2692_;
goto _start;
}
}
}
}
v___jp_2703_:
{
lean_object* v_size_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_size_2706_ = lean_ctor_get(v___y_2704_, 0);
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_nat_add(v_size_2706_, v___x_2707_);
v___x_2709_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2704_, v___x_2708_, v_i_2705_, v___x_2682_, v___x_2678_);
lean_dec(v_i_2705_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2709_;
goto _start;
}
v___jp_2711_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_b_2676_);
lean_dec_ref(v_b_2676_);
v___x_2713_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2712_, v___x_2682_);
switch(lean_obj_tag(v___x_2713_))
{
case 0:
{
lean_object* v_index_2714_; lean_object* v_size_2715_; lean_object* v___x_2716_; 
v_index_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_index_2714_);
lean_dec_ref_known(v___x_2713_, 3);
v_size_2715_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_size_2715_);
v___x_2716_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2712_, v_size_2715_, v_index_2714_, v___x_2682_, v___x_2678_);
lean_dec(v_index_2714_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2716_;
goto _start;
}
case 1:
{
lean_object* v_index_2718_; 
v_index_2718_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_index_2718_);
lean_dec_ref_known(v___x_2713_, 1);
v___y_2704_ = v___x_2712_;
v_i_2705_ = v_index_2718_;
goto v___jp_2703_;
}
default: 
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_unsigned_to_nat(0u);
v___x_2720_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2712_, v___x_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_index_2721_; 
v_index_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_index_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2704_ = v___x_2712_;
v_i_2705_ = v_index_2721_;
goto v___jp_2703_;
}
else
{
lean_dec(v___x_2682_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___x_2712_;
goto _start;
}
}
}
}
}
else
{
return v_b_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__2___boxed(lean_object* v_as_2755_, lean_object* v_i_2756_, lean_object* v_stop_2757_, lean_object* v_b_2758_){
_start:
{
size_t v_i_boxed_2759_; size_t v_stop_boxed_2760_; lean_object* v_res_2761_; 
v_i_boxed_2759_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_stop_boxed_2760_ = lean_unbox_usize(v_stop_2757_);
lean_dec(v_stop_2757_);
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__2(v_as_2755_, v_i_boxed_2759_, v_stop_boxed_2760_, v_b_2758_);
lean_dec_ref(v_as_2755_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2762_){
_start:
{
lean_object* v_alts_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v_cellCount_2773_; lean_object* v___x_2774_; lean_object* v___y_2776_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___y_2787_; lean_object* v_i_2788_; lean_object* v___y_2793_; lean_object* v___y_2802_; lean_object* v_i_2803_; lean_object* v___x_2816_; 
v_alts_2763_ = lean_ctor_get(v_cs_2762_, 3);
v___x_2764_ = lean_array_get_size(v_alts_2763_);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_add(v___x_2764_, v___x_2765_);
v___x_2767_ = lean_unsigned_to_nat(4u);
v___x_2768_ = lean_nat_mul(v___x_2766_, v___x_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_unsigned_to_nat(2u);
v___x_2770_ = lean_nat_add(v___x_2768_, v___x_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_unsigned_to_nat(3u);
v___x_2772_ = lean_nat_div(v___x_2770_, v___x_2771_);
lean_dec(v___x_2770_);
v_cellCount_2773_ = l_Nat_nextPowerOfTwo(v___x_2772_);
lean_dec(v___x_2772_);
v___x_2774_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2773_);
v___x_2781_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2773_);
v___x_2782_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2773_);
lean_inc_ref(v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2774_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
lean_ctor_set(v___x_2783_, 2, v___x_2782_);
v___x_2784_ = lean_box(2);
v___x_2785_ = lean_box(0);
v___x_2816_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2783_, v___x_2784_);
switch(lean_obj_tag(v___x_2816_))
{
case 0:
{
lean_object* v_index_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v___x_2781_);
v_index_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_index_2817_);
lean_dec_ref_known(v___x_2816_, 3);
v___x_2818_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2783_, v___x_2774_, v_index_2817_, v___x_2784_, v___x_2785_);
lean_dec(v_index_2817_);
v___y_2776_ = v___x_2818_;
goto v___jp_2775_;
}
case 1:
{
lean_object* v_index_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_index_2819_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_index_2819_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2820_ = lean_array_get_size(v___x_2781_);
lean_dec_ref(v___x_2781_);
v___x_2821_ = lean_nat_dec_lt(v___x_2765_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec(v_index_2819_);
goto v___jp_2807_;
}
else
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = lean_nat_mul(v___x_2820_, v___x_2771_);
v___x_2823_ = lean_nat_dec_le(v___x_2767_, v___x_2822_);
lean_dec(v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec(v_index_2819_);
goto v___jp_2807_;
}
else
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2783_, v___x_2765_, v_index_2819_, v___x_2784_, v___x_2785_);
lean_dec(v_index_2819_);
v___y_2776_ = v___x_2824_;
goto v___jp_2775_;
}
}
}
default: 
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_array_get_size(v___x_2781_);
lean_dec_ref(v___x_2781_);
v___x_2826_ = lean_nat_dec_lt(v___x_2765_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v___x_2783_);
lean_dec_ref_known(v___x_2783_, 3);
v___y_2793_ = v___x_2827_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = lean_nat_mul(v___x_2825_, v___x_2771_);
v___x_2829_ = lean_nat_dec_le(v___x_2767_, v___x_2828_);
lean_dec(v___x_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v___x_2783_);
lean_dec_ref_known(v___x_2783_, 3);
v___y_2793_ = v___x_2830_;
goto v___jp_2792_;
}
else
{
v___y_2793_ = v___x_2783_;
goto v___jp_2792_;
}
}
}
}
v___jp_2775_:
{
uint8_t v___x_2777_; 
v___x_2777_ = lean_nat_dec_lt(v___x_2774_, v___x_2764_);
if (v___x_2777_ == 0)
{
return v___y_2776_;
}
else
{
size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_usize_of_nat(v___x_2764_);
v___x_2779_ = ((size_t)0ULL);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__2(v_alts_2763_, v___x_2778_, v___x_2779_, v___y_2776_);
return v___x_2780_;
}
}
v___jp_2786_:
{
lean_object* v_size_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_size_2789_ = lean_ctor_get(v___y_2787_, 0);
v___x_2790_ = lean_nat_add(v_size_2789_, v___x_2765_);
v___x_2791_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2787_, v___x_2790_, v_i_2788_, v___x_2784_, v___x_2785_);
lean_dec(v_i_2788_);
v___y_2776_ = v___x_2791_;
goto v___jp_2775_;
}
v___jp_2792_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___y_2793_, v___x_2784_);
switch(lean_obj_tag(v___x_2794_))
{
case 0:
{
lean_object* v_index_2795_; lean_object* v_size_2796_; lean_object* v___x_2797_; 
v_index_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_index_2795_);
lean_dec_ref_known(v___x_2794_, 3);
v_size_2796_ = lean_ctor_get(v___y_2793_, 0);
lean_inc(v_size_2796_);
v___x_2797_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2793_, v_size_2796_, v_index_2795_, v___x_2784_, v___x_2785_);
lean_dec(v_index_2795_);
v___y_2776_ = v___x_2797_;
goto v___jp_2775_;
}
case 1:
{
lean_object* v_index_2798_; 
v_index_2798_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_index_2798_);
lean_dec_ref_known(v___x_2794_, 1);
v___y_2787_ = v___y_2793_;
v_i_2788_ = v_index_2798_;
goto v___jp_2786_;
}
default: 
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2793_, v___x_2774_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_index_2800_; 
v_index_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_index_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2787_ = v___y_2793_;
v_i_2788_ = v_index_2800_;
goto v___jp_2786_;
}
else
{
v___y_2776_ = v___y_2793_;
goto v___jp_2775_;
}
}
}
}
v___jp_2801_:
{
lean_object* v_size_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_size_2804_ = lean_ctor_get(v___y_2802_, 0);
v___x_2805_ = lean_nat_add(v_size_2804_, v___x_2765_);
v___x_2806_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2802_, v___x_2805_, v_i_2803_, v___x_2784_, v___x_2785_);
lean_dec(v_i_2803_);
v___y_2776_ = v___x_2806_;
goto v___jp_2775_;
}
v___jp_2807_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v___x_2783_);
lean_dec_ref_known(v___x_2783_, 3);
v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2808_, v___x_2784_);
switch(lean_obj_tag(v___x_2809_))
{
case 0:
{
lean_object* v_index_2810_; lean_object* v_size_2811_; lean_object* v___x_2812_; 
v_index_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_index_2810_);
lean_dec_ref_known(v___x_2809_, 3);
v_size_2811_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_size_2811_);
v___x_2812_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2808_, v_size_2811_, v_index_2810_, v___x_2784_, v___x_2785_);
lean_dec(v_index_2810_);
v___y_2776_ = v___x_2812_;
goto v___jp_2775_;
}
case 1:
{
lean_object* v_index_2813_; 
v_index_2813_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_index_2813_);
lean_dec_ref_known(v___x_2809_, 1);
v___y_2802_ = v___x_2808_;
v_i_2803_ = v_index_2813_;
goto v___jp_2801_;
}
default: 
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2808_, v___x_2774_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_index_2815_; 
v_index_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_index_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2802_ = v___x_2808_;
v_i_2803_ = v_index_2815_;
goto v___jp_2801_;
}
else
{
v___y_2776_ = v___x_2808_;
goto v___jp_2775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2831_);
lean_dec_ref(v_cs_2831_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2833_, lean_object* v_m_2834_, lean_object* v_query_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2834_, v_query_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___boxed(lean_object* v_00_u03b2_2837_, lean_object* v_m_2838_, lean_object* v_query_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(v_00_u03b2_2837_, v_m_2838_, v_query_2839_);
lean_dec(v_query_2839_);
lean_dec_ref(v_m_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_00_u03b2_2841_, lean_object* v_m_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_m_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_00_u03b2_2844_, lean_object* v_m_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_00_u03b2_2844_, v_m_2845_);
lean_dec_ref(v_m_2845_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2847_, lean_object* v_m_2848_, lean_object* v_query_2849_, lean_object* v_x_2850_, lean_object* v_x_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_m_2848_, v_query_2849_, v_x_2850_, v_x_2851_, v_x_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2855_, lean_object* v_m_2856_, lean_object* v_query_2857_, lean_object* v_x_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2855_, v_m_2856_, v_query_2857_, v_x_2858_, v_x_2859_, v_x_2860_, v_x_2861_);
lean_dec(v_query_2857_);
lean_dec_ref(v_m_2856_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2(lean_object* v_00_u03b2_2863_, lean_object* v_init_2864_, lean_object* v_b_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___redArg(v_init_2864_, v_b_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2867_, lean_object* v_init_2868_, lean_object* v_b_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2(v_00_u03b2_2867_, v_init_2868_, v_b_2869_);
lean_dec_ref(v_b_2869_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2871_, lean_object* v_b_2872_, lean_object* v_acc_2873_, lean_object* v_i_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___redArg(v_b_2872_, v_acc_2873_, v_i_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2876_, lean_object* v_b_2877_, lean_object* v_acc_2878_, lean_object* v_i_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__2_spec__3(v_00_u03b2_2876_, v_b_2877_, v_acc_2878_, v_i_2879_);
lean_dec_ref(v_b_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_decision_2885_; uint8_t v___x_2886_; 
v___x_2884_ = lean_st_ref_get(v_a_2882_);
v_decision_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_decision_2885_);
lean_dec(v___x_2884_);
v___x_2886_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2885_, v_fvar_2881_);
lean_dec_ref(v_decision_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v_fvar_2881_);
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
else
{
lean_object* v___x_2889_; lean_object* v_decision_2890_; lean_object* v_newArms_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2968_; 
v___x_2889_ = lean_st_ref_take(v_a_2882_);
v_decision_2890_ = lean_ctor_get(v___x_2889_, 0);
v_newArms_2891_ = lean_ctor_get(v___x_2889_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2893_ = v___x_2889_;
v_isShared_2894_ = v_isSharedCheck_2968_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_newArms_2891_);
lean_inc(v_decision_2890_);
lean_dec(v___x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2968_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___y_2897_; lean_object* v___x_2903_; lean_object* v___y_2905_; lean_object* v_i_2906_; lean_object* v___y_2912_; lean_object* v___y_2922_; lean_object* v_i_2923_; lean_object* v___x_2938_; 
v___x_2895_ = lean_box(0);
v___x_2903_ = lean_box(2);
v___x_2938_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_decision_2890_, v_fvar_2881_);
switch(lean_obj_tag(v___x_2938_))
{
case 0:
{
lean_object* v_index_2939_; lean_object* v_size_2940_; lean_object* v___x_2941_; 
v_index_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_index_2939_);
lean_dec_ref_known(v___x_2938_, 3);
v_size_2940_ = lean_ctor_get(v_decision_2890_, 0);
lean_inc(v_size_2940_);
v___x_2941_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decision_2890_, v_size_2940_, v_index_2939_, v_fvar_2881_, v___x_2903_);
lean_dec(v_index_2939_);
v___y_2897_ = v___x_2941_;
goto v___jp_2896_;
}
case 1:
{
lean_object* v_index_2942_; lean_object* v_size_2943_; lean_object* v_keyArray_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_index_2942_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_index_2942_);
lean_dec_ref_known(v___x_2938_, 1);
v_size_2943_ = lean_ctor_get(v_decision_2890_, 0);
v_keyArray_2944_ = lean_ctor_get(v_decision_2890_, 1);
v___x_2945_ = lean_unsigned_to_nat(1u);
v___x_2946_ = lean_nat_add(v_size_2943_, v___x_2945_);
v___x_2947_ = lean_array_get_size(v_keyArray_2944_);
v___x_2948_ = lean_nat_dec_lt(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_dec(v___x_2946_);
lean_dec(v_index_2942_);
goto v___jp_2928_;
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2949_ = lean_unsigned_to_nat(4u);
v___x_2950_ = lean_nat_mul(v___x_2946_, v___x_2949_);
v___x_2951_ = lean_unsigned_to_nat(3u);
v___x_2952_ = lean_nat_mul(v___x_2947_, v___x_2951_);
v___x_2953_ = lean_nat_dec_le(v___x_2950_, v___x_2952_);
lean_dec(v___x_2952_);
lean_dec(v___x_2950_);
if (v___x_2953_ == 0)
{
lean_dec(v___x_2946_);
lean_dec(v_index_2942_);
goto v___jp_2928_;
}
else
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decision_2890_, v___x_2946_, v_index_2942_, v_fvar_2881_, v___x_2903_);
lean_dec(v_index_2942_);
v___y_2897_ = v___x_2954_;
goto v___jp_2896_;
}
}
}
default: 
{
lean_object* v_size_2955_; lean_object* v_keyArray_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_size_2955_ = lean_ctor_get(v_decision_2890_, 0);
v_keyArray_2956_ = lean_ctor_get(v_decision_2890_, 1);
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_add(v_size_2955_, v___x_2957_);
v___x_2959_ = lean_array_get_size(v_keyArray_2956_);
v___x_2960_ = lean_nat_dec_lt(v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_dec(v___x_2958_);
v___x_2961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_2890_);
lean_dec_ref(v_decision_2890_);
v___y_2912_ = v___x_2961_;
goto v___jp_2911_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2962_ = lean_unsigned_to_nat(4u);
v___x_2963_ = lean_nat_mul(v___x_2958_, v___x_2962_);
lean_dec(v___x_2958_);
v___x_2964_ = lean_unsigned_to_nat(3u);
v___x_2965_ = lean_nat_mul(v___x_2959_, v___x_2964_);
v___x_2966_ = lean_nat_dec_le(v___x_2963_, v___x_2965_);
lean_dec(v___x_2965_);
lean_dec(v___x_2963_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_2890_);
lean_dec_ref(v_decision_2890_);
v___y_2912_ = v___x_2967_;
goto v___jp_2911_;
}
else
{
v___y_2912_ = v_decision_2890_;
goto v___jp_2911_;
}
}
}
}
v___jp_2896_:
{
lean_object* v___x_2899_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___y_2897_);
v___x_2899_ = v___x_2893_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___y_2897_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_newArms_2891_);
v___x_2899_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_st_ref_put(v_a_2882_, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2895_);
return v___x_2901_;
}
}
v___jp_2904_:
{
lean_object* v_size_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_size_2907_ = lean_ctor_get(v___y_2905_, 0);
v___x_2908_ = lean_unsigned_to_nat(1u);
v___x_2909_ = lean_nat_add(v_size_2907_, v___x_2908_);
v___x_2910_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2905_, v___x_2909_, v_i_2906_, v_fvar_2881_, v___x_2903_);
lean_dec(v_i_2906_);
v___y_2897_ = v___x_2910_;
goto v___jp_2896_;
}
v___jp_2911_:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_2912_, v_fvar_2881_);
switch(lean_obj_tag(v___x_2913_))
{
case 0:
{
lean_object* v_index_2914_; lean_object* v_size_2915_; lean_object* v___x_2916_; 
v_index_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_index_2914_);
lean_dec_ref_known(v___x_2913_, 3);
v_size_2915_ = lean_ctor_get(v___y_2912_, 0);
lean_inc(v_size_2915_);
v___x_2916_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2912_, v_size_2915_, v_index_2914_, v_fvar_2881_, v___x_2903_);
lean_dec(v_index_2914_);
v___y_2897_ = v___x_2916_;
goto v___jp_2896_;
}
case 1:
{
lean_object* v_index_2917_; 
v_index_2917_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_index_2917_);
lean_dec_ref_known(v___x_2913_, 1);
v___y_2905_ = v___y_2912_;
v_i_2906_ = v_index_2917_;
goto v___jp_2904_;
}
default: 
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2912_, v___x_2918_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_index_2920_; 
v_index_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_index_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___y_2905_ = v___y_2912_;
v_i_2906_ = v_index_2920_;
goto v___jp_2904_;
}
else
{
lean_dec(v_fvar_2881_);
v___y_2897_ = v___y_2912_;
goto v___jp_2896_;
}
}
}
}
v___jp_2921_:
{
lean_object* v_size_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_size_2924_ = lean_ctor_get(v___y_2922_, 0);
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_add(v_size_2924_, v___x_2925_);
v___x_2927_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2922_, v___x_2926_, v_i_2923_, v_fvar_2881_, v___x_2903_);
lean_dec(v_i_2923_);
v___y_2897_ = v___x_2927_;
goto v___jp_2896_;
}
v___jp_2928_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_2890_);
lean_dec_ref(v_decision_2890_);
v___x_2930_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_2929_, v_fvar_2881_);
switch(lean_obj_tag(v___x_2930_))
{
case 0:
{
lean_object* v_index_2931_; lean_object* v_size_2932_; lean_object* v___x_2933_; 
v_index_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_index_2931_);
lean_dec_ref_known(v___x_2930_, 3);
v_size_2932_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_size_2932_);
v___x_2933_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2929_, v_size_2932_, v_index_2931_, v_fvar_2881_, v___x_2903_);
lean_dec(v_index_2931_);
v___y_2897_ = v___x_2933_;
goto v___jp_2896_;
}
case 1:
{
lean_object* v_index_2934_; 
v_index_2934_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_index_2934_);
lean_dec_ref_known(v___x_2930_, 1);
v___y_2922_ = v___x_2929_;
v_i_2923_ = v_index_2934_;
goto v___jp_2921_;
}
default: 
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2929_, v___x_2935_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_index_2937_; 
v_index_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_index_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___y_2922_ = v___x_2929_;
v_i_2923_ = v_index_2937_;
goto v___jp_2921_;
}
else
{
lean_dec(v_fvar_2881_);
v___y_2897_ = v___x_2929_;
goto v___jp_2896_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2969_, v_a_2970_);
lean_dec(v_a_2970_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2973_, v_a_2974_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec(v_a_2983_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10(lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_toApplicative_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3064_; 
v___x_2999_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_3000_ = l_StateRefT_x27_instMonad___redArg(v___x_2999_);
v_toApplicative_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3000_, 1);
lean_dec(v_unused_3065_);
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3064_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_toApplicative_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3064_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v_toFunctor_3005_; lean_object* v_toSeq_3006_; lean_object* v_toSeqLeft_3007_; lean_object* v_toSeqRight_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3062_; 
v_toFunctor_3005_ = lean_ctor_get(v_toApplicative_3001_, 0);
v_toSeq_3006_ = lean_ctor_get(v_toApplicative_3001_, 2);
v_toSeqLeft_3007_ = lean_ctor_get(v_toApplicative_3001_, 3);
v_toSeqRight_3008_ = lean_ctor_get(v_toApplicative_3001_, 4);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_toApplicative_3001_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_toApplicative_3001_, 1);
lean_dec(v_unused_3063_);
v___x_3010_ = v_toApplicative_3001_;
v_isShared_3011_ = v_isSharedCheck_3062_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_toSeqRight_3008_);
lean_inc(v_toSeqLeft_3007_);
lean_inc(v_toSeq_3006_);
lean_inc(v_toFunctor_3005_);
lean_dec(v_toApplicative_3001_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3062_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___f_3012_; lean_object* v___f_3013_; lean_object* v___f_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___f_3019_; lean_object* v___x_3021_; 
v___f_3012_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_3013_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3005_);
v___f_3014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3014_, 0, v_toFunctor_3005_);
v___f_3015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3015_, 0, v_toFunctor_3005_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___f_3014_);
lean_ctor_set(v___x_3016_, 1, v___f_3015_);
v___f_3017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3017_, 0, v_toSeqRight_3008_);
v___f_3018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3018_, 0, v_toSeqLeft_3007_);
v___f_3019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3019_, 0, v_toSeq_3006_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 4, v___f_3017_);
lean_ctor_set(v___x_3010_, 3, v___f_3018_);
lean_ctor_set(v___x_3010_, 2, v___f_3019_);
lean_ctor_set(v___x_3010_, 1, v___f_3012_);
lean_ctor_set(v___x_3010_, 0, v___x_3016_);
v___x_3021_ = v___x_3010_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___f_3012_);
lean_ctor_set(v_reuseFailAlloc_3061_, 2, v___f_3019_);
lean_ctor_set(v_reuseFailAlloc_3061_, 3, v___f_3018_);
lean_ctor_set(v_reuseFailAlloc_3061_, 4, v___f_3017_);
v___x_3021_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3023_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 1, v___f_3013_);
lean_ctor_set(v___x_3003_, 0, v___x_3021_);
v___x_3023_ = v___x_3003_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___f_3013_);
v___x_3023_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v_toApplicative_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3058_; 
v___x_3024_ = l_StateRefT_x27_instMonad___redArg(v___x_3023_);
v_toApplicative_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v___x_3024_, 1);
lean_dec(v_unused_3059_);
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3058_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_toApplicative_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3058_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_toFunctor_3029_; lean_object* v_toSeq_3030_; lean_object* v_toSeqLeft_3031_; lean_object* v_toSeqRight_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3056_; 
v_toFunctor_3029_ = lean_ctor_get(v_toApplicative_3025_, 0);
v_toSeq_3030_ = lean_ctor_get(v_toApplicative_3025_, 2);
v_toSeqLeft_3031_ = lean_ctor_get(v_toApplicative_3025_, 3);
v_toSeqRight_3032_ = lean_ctor_get(v_toApplicative_3025_, 4);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_toApplicative_3025_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v_toApplicative_3025_, 1);
lean_dec(v_unused_3057_);
v___x_3034_ = v_toApplicative_3025_;
v_isShared_3035_ = v_isSharedCheck_3056_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_toSeqRight_3032_);
lean_inc(v_toSeqLeft_3031_);
lean_inc(v_toSeq_3030_);
lean_inc(v_toFunctor_3029_);
lean_dec(v_toApplicative_3025_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3056_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___f_3036_; lean_object* v___f_3037_; lean_object* v___f_3038_; lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v___f_3041_; lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___x_3045_; 
v___f_3036_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_3037_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3029_);
v___f_3038_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3038_, 0, v_toFunctor_3029_);
v___f_3039_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3039_, 0, v_toFunctor_3029_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___f_3038_);
lean_ctor_set(v___x_3040_, 1, v___f_3039_);
v___f_3041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3041_, 0, v_toSeqRight_3032_);
v___f_3042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3042_, 0, v_toSeqLeft_3031_);
v___f_3043_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3043_, 0, v_toSeq_3030_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 4, v___f_3041_);
lean_ctor_set(v___x_3034_, 3, v___f_3042_);
lean_ctor_set(v___x_3034_, 2, v___f_3043_);
lean_ctor_set(v___x_3034_, 1, v___f_3036_);
lean_ctor_set(v___x_3034_, 0, v___x_3040_);
v___x_3045_ = v___x_3034_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___f_3036_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v___f_3043_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v___f_3042_);
lean_ctor_set(v_reuseFailAlloc_3055_, 4, v___f_3041_);
v___x_3045_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3047_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___f_3037_);
lean_ctor_set(v___x_3027_, 0, v___x_3045_);
v___x_3047_ = v___x_3027_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___f_3037_);
v___x_3047_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_13676__overap_3052_; lean_object* v___x_3053_; 
v___x_3048_ = l_ReaderT_instMonad___redArg(v___x_3047_);
v___x_3049_ = l_StateRefT_x27_instMonad___redArg(v___x_3048_);
v___x_3050_ = lean_box(0);
v___x_3051_ = l_instInhabitedOfMonad___redArg(v___x_3049_, v___x_3050_);
v___x_13676__overap_3052_ = lean_panic_fn_borrowed(v___x_3051_, v_msg_2991_);
lean_dec(v___x_3051_);
lean_inc(v___y_2997_);
lean_inc_ref(v___y_2996_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc(v___y_2993_);
lean_inc(v___y_2992_);
v___x_3053_ = lean_apply_7(v___x_13676__overap_3052_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, lean_box(0));
return v___x_3053_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10___boxed(lean_object* v_msg_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10(v_msg_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_3075_, lean_object* v_e_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_ty_3085_; lean_object* v_body_3086_; uint8_t v___x_3089_; 
v___x_3089_ = l_Lean_Expr_hasFVar(v_e_3076_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref(v_e_3076_);
lean_dec_ref(v_f_3075_);
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
else
{
switch(lean_obj_tag(v_e_3076_))
{
case 1:
{
lean_object* v_fvarId_3092_; lean_object* v___x_3093_; 
v_fvarId_3092_ = lean_ctor_get(v_e_3076_, 0);
lean_inc(v_fvarId_3092_);
lean_dec_ref_known(v_e_3076_, 1);
lean_inc(v___y_3082_);
lean_inc_ref(v___y_3081_);
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
lean_inc(v___y_3078_);
lean_inc(v___y_3077_);
v___x_3093_ = lean_apply_8(v_f_3075_, v_fvarId_3092_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, lean_box(0));
return v___x_3093_;
}
case 2:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec_ref_known(v_e_3076_, 1);
lean_dec_ref(v_f_3075_);
v___x_3094_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_3095_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10(v___x_3094_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3095_;
}
case 5:
{
lean_object* v_fn_3096_; lean_object* v_arg_3097_; lean_object* v___x_3098_; 
v_fn_3096_ = lean_ctor_get(v_e_3076_, 0);
lean_inc_ref(v_fn_3096_);
v_arg_3097_ = lean_ctor_get(v_e_3076_, 1);
lean_inc_ref(v_arg_3097_);
lean_dec_ref_known(v_e_3076_, 2);
lean_inc_ref(v_f_3075_);
v___x_3098_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3075_, v_fn_3096_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_dec_ref_known(v___x_3098_, 1);
v_e_3076_ = v_arg_3097_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3097_);
lean_dec_ref(v_f_3075_);
return v___x_3098_;
}
}
case 6:
{
lean_object* v_binderType_3100_; lean_object* v_body_3101_; 
v_binderType_3100_ = lean_ctor_get(v_e_3076_, 1);
lean_inc_ref(v_binderType_3100_);
v_body_3101_ = lean_ctor_get(v_e_3076_, 2);
lean_inc_ref(v_body_3101_);
lean_dec_ref_known(v_e_3076_, 3);
v_ty_3085_ = v_binderType_3100_;
v_body_3086_ = v_body_3101_;
goto v___jp_3084_;
}
case 7:
{
lean_object* v_binderType_3102_; lean_object* v_body_3103_; 
v_binderType_3102_ = lean_ctor_get(v_e_3076_, 1);
lean_inc_ref(v_binderType_3102_);
v_body_3103_ = lean_ctor_get(v_e_3076_, 2);
lean_inc_ref(v_body_3103_);
lean_dec_ref_known(v_e_3076_, 3);
v_ty_3085_ = v_binderType_3102_;
v_body_3086_ = v_body_3103_;
goto v___jp_3084_;
}
case 8:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec_ref_known(v_e_3076_, 4);
lean_dec_ref(v_f_3075_);
v___x_3104_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_3105_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10(v___x_3104_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3105_;
}
case 11:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec_ref_known(v_e_3076_, 3);
lean_dec_ref(v_f_3075_);
v___x_3106_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_3107_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__10(v___x_3106_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3107_;
}
default: 
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec_ref(v_e_3076_);
lean_dec_ref(v_f_3075_);
v___x_3108_ = lean_box(0);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
}
v___jp_3084_:
{
lean_object* v___x_3087_; 
lean_inc_ref(v_f_3075_);
v___x_3087_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3075_, v_ty_3085_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_dec_ref_known(v___x_3087_, 1);
v_e_3076_ = v_body_3086_;
goto _start;
}
else
{
lean_dec_ref(v_body_3086_);
lean_dec_ref(v_f_3075_);
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_3110_, lean_object* v_e_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3110_, v_e_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec(v___y_3112_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_3120_, lean_object* v_arg_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
switch(lean_obj_tag(v_arg_3121_))
{
case 0:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v_f_3120_);
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
case 1:
{
lean_object* v_fvarId_3131_; lean_object* v___x_3132_; 
v_fvarId_3131_ = lean_ctor_get(v_arg_3121_, 0);
lean_inc(v_fvarId_3131_);
lean_dec_ref_known(v_arg_3121_, 1);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
lean_inc(v___y_3123_);
lean_inc(v___y_3122_);
v___x_3132_ = lean_apply_8(v_f_3120_, v_fvarId_3131_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, lean_box(0));
return v___x_3132_;
}
default: 
{
lean_object* v_expr_3133_; lean_object* v___x_3134_; 
v_expr_3133_ = lean_ctor_get(v_arg_3121_, 0);
lean_inc_ref(v_expr_3133_);
lean_dec_ref_known(v_arg_3121_, 1);
v___x_3134_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3120_, v_expr_3133_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_3135_, lean_object* v_arg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3135_, v_arg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec(v___y_3137_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg(lean_object* v_f_3145_, lean_object* v_param_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_type_3154_; lean_object* v___x_3155_; 
v_type_3154_ = lean_ctor_get(v_param_3146_, 2);
lean_inc_ref(v_type_3154_);
lean_dec_ref(v_param_3146_);
v___x_3155_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3145_, v_type_3154_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg___boxed(lean_object* v_f_3156_, lean_object* v_param_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg(v_f_3156_, v_param_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___y_3158_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(uint8_t v_pu_3166_, lean_object* v_f_3167_, lean_object* v_as_3168_, size_t v_i_3169_, size_t v_stop_3170_, lean_object* v_b_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_usize_dec_eq(v_i_3169_, v_stop_3170_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_array_uget_borrowed(v_as_3168_, v_i_3169_);
lean_inc(v___x_3180_);
lean_inc_ref(v_f_3167_);
v___x_3181_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg(v_f_3167_, v___x_3180_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; size_t v___x_3183_; size_t v___x_3184_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = ((size_t)1ULL);
v___x_3184_ = lean_usize_add(v_i_3169_, v___x_3183_);
v_i_3169_ = v___x_3184_;
v_b_3171_ = v_a_3182_;
goto _start;
}
else
{
lean_dec_ref(v_f_3167_);
return v___x_3181_;
}
}
else
{
lean_object* v___x_3186_; 
lean_dec_ref(v_f_3167_);
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v_b_3171_);
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7___boxed(lean_object* v_pu_3187_, lean_object* v_f_3188_, lean_object* v_as_3189_, lean_object* v_i_3190_, lean_object* v_stop_3191_, lean_object* v_b_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
uint8_t v_pu_boxed_3200_; size_t v_i_boxed_3201_; size_t v_stop_boxed_3202_; lean_object* v_res_3203_; 
v_pu_boxed_3200_ = lean_unbox(v_pu_3187_);
v_i_boxed_3201_ = lean_unbox_usize(v_i_3190_);
lean_dec(v_i_3190_);
v_stop_boxed_3202_ = lean_unbox_usize(v_stop_3191_);
lean_dec(v_stop_3191_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(v_pu_boxed_3200_, v_f_3188_, v_as_3189_, v_i_boxed_3201_, v_stop_boxed_3202_, v_b_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v_as_3189_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(uint8_t v_pu_3204_, lean_object* v_f_3205_, lean_object* v_as_3206_, size_t v_i_3207_, size_t v_stop_3208_, lean_object* v_b_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_usize_dec_eq(v_i_3207_, v_stop_3208_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_array_uget_borrowed(v_as_3206_, v_i_3207_);
lean_inc(v___x_3218_);
lean_inc_ref(v_f_3205_);
v___x_3219_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3205_, v___x_3218_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; size_t v___x_3221_; size_t v___x_3222_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = ((size_t)1ULL);
v___x_3222_ = lean_usize_add(v_i_3207_, v___x_3221_);
v_i_3207_ = v___x_3222_;
v_b_3209_ = v_a_3220_;
goto _start;
}
else
{
lean_dec_ref(v_f_3205_);
return v___x_3219_;
}
}
else
{
lean_object* v___x_3224_; 
lean_dec_ref(v_f_3205_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_b_3209_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5___boxed(lean_object* v_pu_3225_, lean_object* v_f_3226_, lean_object* v_as_3227_, lean_object* v_i_3228_, lean_object* v_stop_3229_, lean_object* v_b_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_pu_boxed_3238_; size_t v_i_boxed_3239_; size_t v_stop_boxed_3240_; lean_object* v_res_3241_; 
v_pu_boxed_3238_ = lean_unbox(v_pu_3225_);
v_i_boxed_3239_ = lean_unbox_usize(v_i_3228_);
lean_dec(v_i_3228_);
v_stop_boxed_3240_ = lean_unbox_usize(v_stop_3229_);
lean_dec(v_stop_3229_);
v_res_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_boxed_3238_, v_f_3226_, v_as_3227_, v_i_boxed_3239_, v_stop_boxed_3240_, v_b_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v_as_3227_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(uint8_t v_pu_3242_, lean_object* v_f_3243_, lean_object* v_e_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_args_3253_; 
switch(lean_obj_tag(v_e_3244_))
{
case 2:
{
lean_object* v_struct_3267_; lean_object* v___x_3268_; 
v_struct_3267_ = lean_ctor_get(v_e_3244_, 2);
lean_inc(v_struct_3267_);
lean_dec_ref_known(v_e_3244_, 3);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3268_ = lean_apply_8(v_f_3243_, v_struct_3267_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3268_;
}
case 3:
{
lean_object* v_args_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v_args_3269_ = lean_ctor_get(v_e_3244_, 2);
lean_inc_ref(v_args_3269_);
lean_dec_ref_known(v_e_3244_, 3);
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = lean_array_get_size(v_args_3269_);
v___x_3272_ = lean_box(0);
v___x_3273_ = lean_nat_dec_lt(v___x_3270_, v___x_3271_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
lean_dec_ref(v_args_3269_);
lean_dec_ref(v_f_3243_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
return v___x_3274_;
}
else
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_nat_dec_le(v___x_3271_, v___x_3271_);
if (v___x_3275_ == 0)
{
if (v___x_3273_ == 0)
{
lean_object* v___x_3276_; 
lean_dec_ref(v_args_3269_);
lean_dec_ref(v_f_3243_);
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3272_);
return v___x_3276_;
}
else
{
size_t v___x_3277_; size_t v___x_3278_; lean_object* v___x_3279_; 
v___x_3277_ = ((size_t)0ULL);
v___x_3278_ = lean_usize_of_nat(v___x_3271_);
v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3269_, v___x_3277_, v___x_3278_, v___x_3272_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3269_);
return v___x_3279_;
}
}
else
{
size_t v___x_3280_; size_t v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = ((size_t)0ULL);
v___x_3281_ = lean_usize_of_nat(v___x_3271_);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3269_, v___x_3280_, v___x_3281_, v___x_3272_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3269_);
return v___x_3282_;
}
}
}
case 4:
{
lean_object* v_fvarId_3283_; lean_object* v_args_3284_; lean_object* v___x_3285_; 
v_fvarId_3283_ = lean_ctor_get(v_e_3244_, 0);
lean_inc(v_fvarId_3283_);
v_args_3284_ = lean_ctor_get(v_e_3244_, 1);
lean_inc_ref(v_args_3284_);
lean_dec_ref_known(v_e_3244_, 2);
lean_inc_ref(v_f_3243_);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3285_ = lean_apply_8(v_f_3243_, v_fvarId_3283_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3306_; 
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v___x_3285_, 0);
lean_dec(v_unused_3307_);
v___x_3287_ = v___x_3285_;
v_isShared_3288_ = v_isSharedCheck_3306_;
goto v_resetjp_3286_;
}
else
{
lean_dec(v___x_3285_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3306_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = lean_array_get_size(v_args_3284_);
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_nat_dec_lt(v___x_3289_, v___x_3290_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref(v_args_3284_);
lean_dec_ref(v_f_3243_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3291_);
v___x_3294_ = v___x_3287_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3291_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
else
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_nat_dec_le(v___x_3290_, v___x_3290_);
if (v___x_3296_ == 0)
{
if (v___x_3292_ == 0)
{
lean_object* v___x_3298_; 
lean_dec_ref(v_args_3284_);
lean_dec_ref(v_f_3243_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3291_);
v___x_3298_ = v___x_3287_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3291_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; 
lean_del_object(v___x_3287_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = lean_usize_of_nat(v___x_3290_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3284_, v___x_3300_, v___x_3301_, v___x_3291_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3284_);
return v___x_3302_;
}
}
else
{
size_t v___x_3303_; size_t v___x_3304_; lean_object* v___x_3305_; 
lean_del_object(v___x_3287_);
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = lean_usize_of_nat(v___x_3290_);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3284_, v___x_3303_, v___x_3304_, v___x_3291_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3284_);
return v___x_3305_;
}
}
}
}
else
{
lean_dec_ref(v_args_3284_);
lean_dec_ref(v_f_3243_);
return v___x_3285_;
}
}
case 5:
{
lean_object* v_args_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v_args_3308_ = lean_ctor_get(v_e_3244_, 1);
lean_inc_ref(v_args_3308_);
lean_dec_ref_known(v_e_3244_, 2);
v___x_3309_ = lean_unsigned_to_nat(0u);
v___x_3310_ = lean_array_get_size(v_args_3308_);
v___x_3311_ = lean_box(0);
v___x_3312_ = lean_nat_dec_lt(v___x_3309_, v___x_3310_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec_ref(v_args_3308_);
lean_dec_ref(v_f_3243_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
return v___x_3313_;
}
else
{
uint8_t v___x_3314_; 
v___x_3314_ = lean_nat_dec_le(v___x_3310_, v___x_3310_);
if (v___x_3314_ == 0)
{
if (v___x_3312_ == 0)
{
lean_object* v___x_3315_; 
lean_dec_ref(v_args_3308_);
lean_dec_ref(v_f_3243_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3311_);
return v___x_3315_;
}
else
{
size_t v___x_3316_; size_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = ((size_t)0ULL);
v___x_3317_ = lean_usize_of_nat(v___x_3310_);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3308_, v___x_3316_, v___x_3317_, v___x_3311_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3308_);
return v___x_3318_;
}
}
else
{
size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = ((size_t)0ULL);
v___x_3320_ = lean_usize_of_nat(v___x_3310_);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3308_, v___x_3319_, v___x_3320_, v___x_3311_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3308_);
return v___x_3321_;
}
}
}
case 6:
{
lean_object* v_var_3322_; lean_object* v___x_3323_; 
v_var_3322_ = lean_ctor_get(v_e_3244_, 1);
lean_inc(v_var_3322_);
lean_dec_ref_known(v_e_3244_, 2);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3323_ = lean_apply_8(v_f_3243_, v_var_3322_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3323_;
}
case 7:
{
lean_object* v_var_3324_; lean_object* v___x_3325_; 
v_var_3324_ = lean_ctor_get(v_e_3244_, 1);
lean_inc(v_var_3324_);
lean_dec_ref_known(v_e_3244_, 2);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3325_ = lean_apply_8(v_f_3243_, v_var_3324_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3325_;
}
case 8:
{
lean_object* v_var_3326_; lean_object* v___x_3327_; 
v_var_3326_ = lean_ctor_get(v_e_3244_, 2);
lean_inc(v_var_3326_);
lean_dec_ref_known(v_e_3244_, 3);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3327_ = lean_apply_8(v_f_3243_, v_var_3326_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3327_;
}
case 9:
{
lean_object* v_args_3328_; 
v_args_3328_ = lean_ctor_get(v_e_3244_, 1);
lean_inc_ref(v_args_3328_);
lean_dec_ref_known(v_e_3244_, 2);
v_args_3253_ = v_args_3328_;
goto v___jp_3252_;
}
case 10:
{
lean_object* v_args_3329_; 
v_args_3329_ = lean_ctor_get(v_e_3244_, 1);
lean_inc_ref(v_args_3329_);
lean_dec_ref_known(v_e_3244_, 2);
v_args_3253_ = v_args_3329_;
goto v___jp_3252_;
}
case 11:
{
lean_object* v_var_3330_; lean_object* v___x_3331_; 
v_var_3330_ = lean_ctor_get(v_e_3244_, 1);
lean_inc(v_var_3330_);
lean_dec_ref_known(v_e_3244_, 2);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3331_ = lean_apply_8(v_f_3243_, v_var_3330_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3331_;
}
case 12:
{
lean_object* v_var_3332_; lean_object* v_args_3333_; lean_object* v___x_3334_; 
v_var_3332_ = lean_ctor_get(v_e_3244_, 0);
lean_inc(v_var_3332_);
v_args_3333_ = lean_ctor_get(v_e_3244_, 2);
lean_inc_ref(v_args_3333_);
lean_dec_ref_known(v_e_3244_, 3);
lean_inc_ref(v_f_3243_);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3334_ = lean_apply_8(v_f_3243_, v_var_3332_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3355_; 
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; 
v_unused_3356_ = lean_ctor_get(v___x_3334_, 0);
lean_dec(v_unused_3356_);
v___x_3336_ = v___x_3334_;
v_isShared_3337_ = v_isSharedCheck_3355_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3334_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3355_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_array_get_size(v_args_3333_);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_nat_dec_lt(v___x_3338_, v___x_3339_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3343_; 
lean_dec_ref(v_args_3333_);
lean_dec_ref(v_f_3243_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3340_);
v___x_3343_ = v___x_3336_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3340_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_nat_dec_le(v___x_3339_, v___x_3339_);
if (v___x_3345_ == 0)
{
if (v___x_3341_ == 0)
{
lean_object* v___x_3347_; 
lean_dec_ref(v_args_3333_);
lean_dec_ref(v_f_3243_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3340_);
v___x_3347_ = v___x_3336_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3340_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
else
{
size_t v___x_3349_; size_t v___x_3350_; lean_object* v___x_3351_; 
lean_del_object(v___x_3336_);
v___x_3349_ = ((size_t)0ULL);
v___x_3350_ = lean_usize_of_nat(v___x_3339_);
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3333_, v___x_3349_, v___x_3350_, v___x_3340_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3333_);
return v___x_3351_;
}
}
else
{
size_t v___x_3352_; size_t v___x_3353_; lean_object* v___x_3354_; 
lean_del_object(v___x_3336_);
v___x_3352_ = ((size_t)0ULL);
v___x_3353_ = lean_usize_of_nat(v___x_3339_);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3333_, v___x_3352_, v___x_3353_, v___x_3340_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3333_);
return v___x_3354_;
}
}
}
}
else
{
lean_dec_ref(v_args_3333_);
lean_dec_ref(v_f_3243_);
return v___x_3334_;
}
}
case 13:
{
lean_object* v_fvarId_3357_; lean_object* v___x_3358_; 
v_fvarId_3357_ = lean_ctor_get(v_e_3244_, 1);
lean_inc(v_fvarId_3357_);
lean_dec_ref_known(v_e_3244_, 2);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3358_ = lean_apply_8(v_f_3243_, v_fvarId_3357_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3358_;
}
case 14:
{
lean_object* v_fvarId_3359_; lean_object* v___x_3360_; 
v_fvarId_3359_ = lean_ctor_get(v_e_3244_, 0);
lean_inc(v_fvarId_3359_);
lean_dec_ref_known(v_e_3244_, 1);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3360_ = lean_apply_8(v_f_3243_, v_fvarId_3359_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3360_;
}
case 15:
{
lean_object* v_fvarId_3361_; lean_object* v___x_3362_; 
v_fvarId_3361_ = lean_ctor_get(v_e_3244_, 0);
lean_inc(v_fvarId_3361_);
lean_dec_ref_known(v_e_3244_, 1);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc(v___y_3245_);
v___x_3362_ = lean_apply_8(v_f_3243_, v_fvarId_3361_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, lean_box(0));
return v___x_3362_;
}
default: 
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v_e_3244_);
lean_dec_ref(v_f_3243_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
v___jp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = lean_array_get_size(v_args_3253_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_nat_dec_lt(v___x_3254_, v___x_3255_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
lean_dec_ref(v_args_3253_);
lean_dec_ref(v_f_3243_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
return v___x_3258_;
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_nat_dec_le(v___x_3255_, v___x_3255_);
if (v___x_3259_ == 0)
{
if (v___x_3257_ == 0)
{
lean_object* v___x_3260_; 
lean_dec_ref(v_args_3253_);
lean_dec_ref(v_f_3243_);
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3256_);
return v___x_3260_;
}
else
{
size_t v___x_3261_; size_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = lean_usize_of_nat(v___x_3255_);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3253_, v___x_3261_, v___x_3262_, v___x_3256_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3253_);
return v___x_3263_;
}
}
else
{
size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = ((size_t)0ULL);
v___x_3265_ = lean_usize_of_nat(v___x_3255_);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3242_, v_f_3243_, v_args_3253_, v___x_3264_, v___x_3265_, v___x_3256_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref(v_args_3253_);
return v___x_3266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3___boxed(lean_object* v_pu_3365_, lean_object* v_f_3366_, lean_object* v_e_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
uint8_t v_pu_boxed_3375_; lean_object* v_res_3376_; 
v_pu_boxed_3375_ = lean_unbox(v_pu_3365_);
v_res_3376_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(v_pu_boxed_3375_, v_f_3366_, v_e_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3368_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_3377_, lean_object* v_f_3378_, lean_object* v_decl_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_type_3387_; lean_object* v_value_3388_; lean_object* v___x_3389_; 
v_type_3387_ = lean_ctor_get(v_decl_3379_, 2);
lean_inc_ref(v_type_3387_);
v_value_3388_ = lean_ctor_get(v_decl_3379_, 3);
lean_inc(v_value_3388_);
lean_dec_ref(v_decl_3379_);
lean_inc_ref(v_f_3378_);
v___x_3389_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3378_, v_type_3387_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v___x_3390_; 
lean_dec_ref_known(v___x_3389_, 1);
v___x_3390_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(v_pu_3377_, v_f_3378_, v_value_3388_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3390_;
}
else
{
lean_dec(v_value_3388_);
lean_dec_ref(v_f_3378_);
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_3391_, lean_object* v_f_3392_, lean_object* v_decl_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v_pu_boxed_3401_; lean_object* v_res_3402_; 
v_pu_boxed_3401_ = lean_unbox(v_pu_3391_);
v_res_3402_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_3401_, v_f_3392_, v_decl_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec(v___y_3394_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg(lean_object* v_alt_3403_, lean_object* v_f_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
switch(lean_obj_tag(v_alt_3403_))
{
case 0:
{
lean_object* v_code_3412_; lean_object* v___x_3413_; 
v_code_3412_ = lean_ctor_get(v_alt_3403_, 2);
lean_inc_ref(v_code_3412_);
lean_dec_ref_known(v_alt_3403_, 3);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc(v___y_3405_);
v___x_3413_ = lean_apply_8(v_f_3404_, v_code_3412_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, lean_box(0));
return v___x_3413_;
}
case 1:
{
lean_object* v_code_3414_; lean_object* v___x_3415_; 
v_code_3414_ = lean_ctor_get(v_alt_3403_, 1);
lean_inc_ref(v_code_3414_);
lean_dec_ref_known(v_alt_3403_, 2);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc(v___y_3405_);
v___x_3415_ = lean_apply_8(v_f_3404_, v_code_3414_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, lean_box(0));
return v___x_3415_;
}
default: 
{
lean_object* v_code_3416_; lean_object* v___x_3417_; 
v_code_3416_ = lean_ctor_get(v_alt_3403_, 0);
lean_inc_ref(v_code_3416_);
lean_dec_ref_known(v_alt_3403_, 1);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3406_);
lean_inc(v___y_3405_);
v___x_3417_ = lean_apply_8(v_f_3404_, v_code_3416_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, lean_box(0));
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_alt_3418_, lean_object* v_f_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg(v_alt_3418_, v_f_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec(v___y_3420_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___lam__0___boxed(lean_object* v_pu_3428_, lean_object* v_f_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v_pu_boxed_3438_; lean_object* v_res_3439_; 
v_pu_boxed_3438_ = lean_unbox(v_pu_3428_);
v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___lam__0(v_pu_boxed_3438_, v_f_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3431_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10(uint8_t v_pu_3440_, lean_object* v_f_3441_, lean_object* v_as_3442_, size_t v_i_3443_, size_t v_stop_3444_, lean_object* v_b_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_usize_dec_eq(v_i_3443_, v_stop_3444_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; lean_object* v___f_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3454_ = lean_box(v_pu_3440_);
lean_inc_ref(v_f_3441_);
v___f_3455_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3455_, 0, v___x_3454_);
lean_closure_set(v___f_3455_, 1, v_f_3441_);
v___x_3456_ = lean_array_uget_borrowed(v_as_3442_, v_i_3443_);
lean_inc(v___x_3456_);
v___x_3457_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg(v___x_3456_, v___f_3455_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; size_t v___x_3459_; size_t v___x_3460_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3443_, v___x_3459_);
v_i_3443_ = v___x_3460_;
v_b_3445_ = v_a_3458_;
goto _start;
}
else
{
lean_dec_ref(v_f_3441_);
return v___x_3457_;
}
}
else
{
lean_object* v___x_3462_; 
lean_dec_ref(v_f_3441_);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_b_3445_);
return v___x_3462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_3463_, lean_object* v_f_3464_, lean_object* v_c_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
switch(lean_obj_tag(v_c_3465_))
{
case 0:
{
lean_object* v_decl_3473_; lean_object* v_k_3474_; lean_object* v___x_3475_; 
v_decl_3473_ = lean_ctor_get(v_c_3465_, 0);
lean_inc_ref(v_decl_3473_);
v_k_3474_ = lean_ctor_get(v_c_3465_, 1);
lean_inc_ref(v_k_3474_);
lean_dec_ref_known(v_c_3465_, 2);
lean_inc_ref(v_f_3464_);
v___x_3475_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_3463_, v_f_3464_, v_decl_3473_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec_ref_known(v___x_3475_, 1);
v_c_3465_ = v_k_3474_;
goto _start;
}
else
{
lean_dec_ref(v_k_3474_);
lean_dec_ref(v_f_3464_);
return v___x_3475_;
}
}
case 3:
{
lean_object* v_fvarId_3477_; lean_object* v_args_3478_; lean_object* v___x_3479_; 
v_fvarId_3477_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3477_);
v_args_3478_ = lean_ctor_get(v_c_3465_, 1);
lean_inc_ref(v_args_3478_);
lean_dec_ref_known(v_c_3465_, 2);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3479_ = lean_apply_8(v_f_3464_, v_fvarId_3477_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3501_);
v___x_3481_ = v___x_3479_;
v_isShared_3482_ = v_isSharedCheck_3500_;
goto v_resetjp_3480_;
}
else
{
lean_dec(v___x_3479_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3500_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_array_get_size(v_args_3478_);
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_nat_dec_lt(v___x_3483_, v___x_3484_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3488_; 
lean_dec_ref(v_args_3478_);
lean_dec_ref(v_f_3464_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3485_);
v___x_3488_ = v___x_3481_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3485_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
uint8_t v___x_3490_; 
v___x_3490_ = lean_nat_dec_le(v___x_3484_, v___x_3484_);
if (v___x_3490_ == 0)
{
if (v___x_3486_ == 0)
{
lean_object* v___x_3492_; 
lean_dec_ref(v_args_3478_);
lean_dec_ref(v_f_3464_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3485_);
v___x_3492_ = v___x_3481_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3485_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
else
{
size_t v___x_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
lean_del_object(v___x_3481_);
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = lean_usize_of_nat(v___x_3484_);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3463_, v_f_3464_, v_args_3478_, v___x_3494_, v___x_3495_, v___x_3485_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v_args_3478_);
return v___x_3496_;
}
}
else
{
size_t v___x_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
lean_del_object(v___x_3481_);
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = lean_usize_of_nat(v___x_3484_);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__5(v_pu_3463_, v_f_3464_, v_args_3478_, v___x_3497_, v___x_3498_, v___x_3485_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v_args_3478_);
return v___x_3499_;
}
}
}
}
else
{
lean_dec_ref(v_args_3478_);
lean_dec_ref(v_f_3464_);
return v___x_3479_;
}
}
case 4:
{
lean_object* v_cases_3502_; lean_object* v_resultType_3503_; lean_object* v_discr_3504_; lean_object* v_alts_3505_; lean_object* v___x_3506_; 
v_cases_3502_ = lean_ctor_get(v_c_3465_, 0);
lean_inc_ref(v_cases_3502_);
lean_dec_ref_known(v_c_3465_, 1);
v_resultType_3503_ = lean_ctor_get(v_cases_3502_, 1);
lean_inc_ref(v_resultType_3503_);
v_discr_3504_ = lean_ctor_get(v_cases_3502_, 2);
lean_inc(v_discr_3504_);
v_alts_3505_ = lean_ctor_get(v_cases_3502_, 3);
lean_inc_ref(v_alts_3505_);
lean_dec_ref(v_cases_3502_);
lean_inc_ref(v_f_3464_);
v___x_3506_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3464_, v_resultType_3503_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; 
lean_dec_ref_known(v___x_3506_, 1);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3507_ = lean_apply_8(v_f_3464_, v_discr_3504_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3528_; 
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v___x_3507_, 0);
lean_dec(v_unused_3529_);
v___x_3509_ = v___x_3507_;
v_isShared_3510_ = v_isSharedCheck_3528_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v___x_3507_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3528_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_array_get_size(v_alts_3505_);
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_nat_dec_lt(v___x_3511_, v___x_3512_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3516_; 
lean_dec_ref(v_alts_3505_);
lean_dec_ref(v_f_3464_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3513_);
v___x_3516_ = v___x_3509_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3513_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
else
{
uint8_t v___x_3518_; 
v___x_3518_ = lean_nat_dec_le(v___x_3512_, v___x_3512_);
if (v___x_3518_ == 0)
{
if (v___x_3514_ == 0)
{
lean_object* v___x_3520_; 
lean_dec_ref(v_alts_3505_);
lean_dec_ref(v_f_3464_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3513_);
v___x_3520_ = v___x_3509_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3513_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
else
{
size_t v___x_3522_; size_t v___x_3523_; lean_object* v___x_3524_; 
lean_del_object(v___x_3509_);
v___x_3522_ = ((size_t)0ULL);
v___x_3523_ = lean_usize_of_nat(v___x_3512_);
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10(v_pu_3463_, v_f_3464_, v_alts_3505_, v___x_3522_, v___x_3523_, v___x_3513_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v_alts_3505_);
return v___x_3524_;
}
}
else
{
size_t v___x_3525_; size_t v___x_3526_; lean_object* v___x_3527_; 
lean_del_object(v___x_3509_);
v___x_3525_ = ((size_t)0ULL);
v___x_3526_ = lean_usize_of_nat(v___x_3512_);
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10(v_pu_3463_, v_f_3464_, v_alts_3505_, v___x_3525_, v___x_3526_, v___x_3513_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v_alts_3505_);
return v___x_3527_;
}
}
}
}
else
{
lean_dec_ref(v_alts_3505_);
lean_dec_ref(v_f_3464_);
return v___x_3507_;
}
}
else
{
lean_dec_ref(v_alts_3505_);
lean_dec(v_discr_3504_);
lean_dec_ref(v_f_3464_);
return v___x_3506_;
}
}
case 5:
{
lean_object* v_fvarId_3530_; lean_object* v___x_3531_; 
v_fvarId_3530_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3530_);
lean_dec_ref_known(v_c_3465_, 1);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3531_ = lean_apply_8(v_f_3464_, v_fvarId_3530_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
return v___x_3531_;
}
case 6:
{
lean_object* v_type_3532_; lean_object* v___x_3533_; 
v_type_3532_ = lean_ctor_get(v_c_3465_, 0);
lean_inc_ref(v_type_3532_);
lean_dec_ref_known(v_c_3465_, 1);
v___x_3533_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3464_, v_type_3532_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
return v___x_3533_;
}
case 7:
{
lean_object* v_fvarId_3534_; lean_object* v_y_3535_; lean_object* v_k_3536_; lean_object* v___x_3537_; 
v_fvarId_3534_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3534_);
v_y_3535_ = lean_ctor_get(v_c_3465_, 2);
lean_inc(v_y_3535_);
v_k_3536_ = lean_ctor_get(v_c_3465_, 3);
lean_inc_ref(v_k_3536_);
lean_dec_ref_known(v_c_3465_, 4);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3537_ = lean_apply_8(v_f_3464_, v_fvarId_3534_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3537_, 1);
lean_inc_ref(v_f_3464_);
v___x_3538_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3464_, v_y_3535_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_dec_ref_known(v___x_3538_, 1);
v_c_3465_ = v_k_3536_;
goto _start;
}
else
{
lean_dec_ref(v_k_3536_);
lean_dec_ref(v_f_3464_);
return v___x_3538_;
}
}
else
{
lean_dec_ref(v_k_3536_);
lean_dec(v_y_3535_);
lean_dec_ref(v_f_3464_);
return v___x_3537_;
}
}
case 8:
{
lean_object* v_fvarId_3540_; lean_object* v_y_3541_; lean_object* v_k_3542_; lean_object* v___x_3543_; 
v_fvarId_3540_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3540_);
v_y_3541_ = lean_ctor_get(v_c_3465_, 2);
lean_inc(v_y_3541_);
v_k_3542_ = lean_ctor_get(v_c_3465_, 3);
lean_inc_ref(v_k_3542_);
lean_dec_ref_known(v_c_3465_, 4);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3543_ = lean_apply_8(v_f_3464_, v_fvarId_3540_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3544_; 
lean_dec_ref_known(v___x_3543_, 1);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3544_ = lean_apply_8(v_f_3464_, v_y_3541_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_dec_ref_known(v___x_3544_, 1);
v_c_3465_ = v_k_3542_;
goto _start;
}
else
{
lean_dec_ref(v_k_3542_);
lean_dec_ref(v_f_3464_);
return v___x_3544_;
}
}
else
{
lean_dec_ref(v_k_3542_);
lean_dec(v_y_3541_);
lean_dec_ref(v_f_3464_);
return v___x_3543_;
}
}
case 9:
{
lean_object* v_fvarId_3546_; lean_object* v_y_3547_; lean_object* v_ty_3548_; lean_object* v_k_3549_; lean_object* v___x_3550_; 
v_fvarId_3546_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3546_);
v_y_3547_ = lean_ctor_get(v_c_3465_, 3);
lean_inc(v_y_3547_);
v_ty_3548_ = lean_ctor_get(v_c_3465_, 4);
lean_inc_ref(v_ty_3548_);
v_k_3549_ = lean_ctor_get(v_c_3465_, 5);
lean_inc_ref(v_k_3549_);
lean_dec_ref_known(v_c_3465_, 6);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3550_ = lean_apply_8(v_f_3464_, v_fvarId_3546_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref_known(v___x_3550_, 1);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3551_ = lean_apply_8(v_f_3464_, v_y_3547_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
lean_inc_ref(v_f_3464_);
v___x_3552_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3464_, v_ty_3548_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_dec_ref_known(v___x_3552_, 1);
v_c_3465_ = v_k_3549_;
goto _start;
}
else
{
lean_dec_ref(v_k_3549_);
lean_dec_ref(v_f_3464_);
return v___x_3552_;
}
}
else
{
lean_dec_ref(v_k_3549_);
lean_dec_ref(v_ty_3548_);
lean_dec_ref(v_f_3464_);
return v___x_3551_;
}
}
else
{
lean_dec_ref(v_k_3549_);
lean_dec_ref(v_ty_3548_);
lean_dec(v_y_3547_);
lean_dec_ref(v_f_3464_);
return v___x_3550_;
}
}
case 10:
{
lean_object* v_fvarId_3554_; lean_object* v_k_3555_; lean_object* v___x_3556_; 
v_fvarId_3554_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3554_);
v_k_3555_ = lean_ctor_get(v_c_3465_, 2);
lean_inc_ref(v_k_3555_);
lean_dec_ref_known(v_c_3465_, 3);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3556_ = lean_apply_8(v_f_3464_, v_fvarId_3554_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref_known(v___x_3556_, 1);
v_c_3465_ = v_k_3555_;
goto _start;
}
else
{
lean_dec_ref(v_k_3555_);
lean_dec_ref(v_f_3464_);
return v___x_3556_;
}
}
case 11:
{
lean_object* v_fvarId_3558_; lean_object* v_k_3559_; lean_object* v___x_3560_; 
v_fvarId_3558_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3558_);
v_k_3559_ = lean_ctor_get(v_c_3465_, 2);
lean_inc_ref(v_k_3559_);
lean_dec_ref_known(v_c_3465_, 3);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3560_ = lean_apply_8(v_f_3464_, v_fvarId_3558_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_dec_ref_known(v___x_3560_, 1);
v_c_3465_ = v_k_3559_;
goto _start;
}
else
{
lean_dec_ref(v_k_3559_);
lean_dec_ref(v_f_3464_);
return v___x_3560_;
}
}
case 12:
{
lean_object* v_fvarId_3562_; lean_object* v_k_3563_; lean_object* v___x_3564_; 
v_fvarId_3562_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3562_);
v_k_3563_ = lean_ctor_get(v_c_3465_, 3);
lean_inc_ref(v_k_3563_);
lean_dec_ref_known(v_c_3465_, 4);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3564_ = lean_apply_8(v_f_3464_, v_fvarId_3562_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_dec_ref_known(v___x_3564_, 1);
v_c_3465_ = v_k_3563_;
goto _start;
}
else
{
lean_dec_ref(v_k_3563_);
lean_dec_ref(v_f_3464_);
return v___x_3564_;
}
}
case 13:
{
lean_object* v_fvarId_3566_; lean_object* v_k_3567_; lean_object* v___x_3568_; 
v_fvarId_3566_ = lean_ctor_get(v_c_3465_, 0);
lean_inc(v_fvarId_3566_);
v_k_3567_ = lean_ctor_get(v_c_3465_, 1);
lean_inc_ref(v_k_3567_);
lean_dec_ref_known(v_c_3465_, 2);
lean_inc_ref(v_f_3464_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc(v___y_3466_);
v___x_3568_ = lean_apply_8(v_f_3464_, v_fvarId_3566_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, lean_box(0));
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_dec_ref_known(v___x_3568_, 1);
v_c_3465_ = v_k_3567_;
goto _start;
}
else
{
lean_dec_ref(v_k_3567_);
lean_dec_ref(v_f_3464_);
return v___x_3568_;
}
}
default: 
{
lean_object* v_decl_3570_; lean_object* v_k_3571_; lean_object* v_params_3572_; lean_object* v_type_3573_; lean_object* v_value_3574_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v_decl_3570_ = lean_ctor_get(v_c_3465_, 0);
lean_inc_ref(v_decl_3570_);
v_k_3571_ = lean_ctor_get(v_c_3465_, 1);
lean_inc_ref(v_k_3571_);
lean_dec_ref(v_c_3465_);
v_params_3572_ = lean_ctor_get(v_decl_3570_, 2);
lean_inc_ref(v_params_3572_);
v_type_3573_ = lean_ctor_get(v_decl_3570_, 3);
lean_inc_ref(v_type_3573_);
v_value_3574_ = lean_ctor_get(v_decl_3570_, 4);
lean_inc_ref(v_value_3574_);
lean_dec_ref(v_decl_3570_);
v___x_3585_ = lean_unsigned_to_nat(0u);
v___x_3586_ = lean_array_get_size(v_params_3572_);
v___x_3587_ = lean_nat_dec_lt(v___x_3585_, v___x_3586_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; 
lean_dec_ref(v_params_3572_);
lean_inc_ref(v_f_3464_);
v___x_3588_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3464_, v_type_3573_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; 
lean_dec_ref_known(v___x_3588_, 1);
lean_inc_ref(v_f_3464_);
v___x_3589_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3463_, v_f_3464_, v_value_3574_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_dec_ref_known(v___x_3589_, 1);
v_c_3465_ = v_k_3571_;
goto _start;
}
else
{
lean_dec_ref(v_k_3571_);
lean_dec_ref(v_f_3464_);
return v___x_3589_;
}
}
else
{
lean_dec_ref(v_value_3574_);
lean_dec_ref(v_k_3571_);
lean_dec_ref(v_f_3464_);
return v___x_3588_;
}
}
else
{
lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_nat_dec_le(v___x_3586_, v___x_3586_);
if (v___x_3592_ == 0)
{
if (v___x_3587_ == 0)
{
lean_dec_ref(v_params_3572_);
v___y_3576_ = v___y_3466_;
v___y_3577_ = v___y_3467_;
v___y_3578_ = v___y_3468_;
v___y_3579_ = v___y_3469_;
v___y_3580_ = v___y_3470_;
v___y_3581_ = v___y_3471_;
goto v___jp_3575_;
}
else
{
size_t v___x_3593_; size_t v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = ((size_t)0ULL);
v___x_3594_ = lean_usize_of_nat(v___x_3586_);
lean_inc_ref(v_f_3464_);
v___x_3595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(v_pu_3463_, v_f_3464_, v_params_3572_, v___x_3593_, v___x_3594_, v___x_3591_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v_params_3572_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_dec_ref_known(v___x_3595_, 1);
v___y_3576_ = v___y_3466_;
v___y_3577_ = v___y_3467_;
v___y_3578_ = v___y_3468_;
v___y_3579_ = v___y_3469_;
v___y_3580_ = v___y_3470_;
v___y_3581_ = v___y_3471_;
goto v___jp_3575_;
}
else
{
lean_dec_ref(v_value_3574_);
lean_dec_ref(v_type_3573_);
lean_dec_ref(v_k_3571_);
lean_dec_ref(v_f_3464_);
return v___x_3595_;
}
}
}
else
{
size_t v___x_3596_; size_t v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = ((size_t)0ULL);
v___x_3597_ = lean_usize_of_nat(v___x_3586_);
lean_inc_ref(v_f_3464_);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(v_pu_3463_, v_f_3464_, v_params_3572_, v___x_3596_, v___x_3597_, v___x_3591_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v_params_3572_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_dec_ref_known(v___x_3598_, 1);
v___y_3576_ = v___y_3466_;
v___y_3577_ = v___y_3467_;
v___y_3578_ = v___y_3468_;
v___y_3579_ = v___y_3469_;
v___y_3580_ = v___y_3470_;
v___y_3581_ = v___y_3471_;
goto v___jp_3575_;
}
else
{
lean_dec_ref(v_value_3574_);
lean_dec_ref(v_type_3573_);
lean_dec_ref(v_k_3571_);
lean_dec_ref(v_f_3464_);
return v___x_3598_;
}
}
}
v___jp_3575_:
{
lean_object* v___x_3582_; 
lean_inc_ref(v_f_3464_);
v___x_3582_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3464_, v_type_3573_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; 
lean_dec_ref_known(v___x_3582_, 1);
lean_inc_ref(v_f_3464_);
v___x_3583_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3463_, v_f_3464_, v_value_3574_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_dec_ref_known(v___x_3583_, 1);
v_c_3465_ = v_k_3571_;
v___y_3466_ = v___y_3576_;
v___y_3467_ = v___y_3577_;
v___y_3468_ = v___y_3578_;
v___y_3469_ = v___y_3579_;
v___y_3470_ = v___y_3580_;
v___y_3471_ = v___y_3581_;
goto _start;
}
else
{
lean_dec_ref(v_k_3571_);
lean_dec_ref(v_f_3464_);
return v___x_3583_;
}
}
else
{
lean_dec_ref(v_value_3574_);
lean_dec_ref(v_k_3571_);
lean_dec_ref(v_f_3464_);
return v___x_3582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___lam__0(uint8_t v_pu_3599_, lean_object* v_f_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3599_, v_f_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10___boxed(lean_object* v_pu_3610_, lean_object* v_f_3611_, lean_object* v_as_3612_, lean_object* v_i_3613_, lean_object* v_stop_3614_, lean_object* v_b_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
uint8_t v_pu_boxed_3623_; size_t v_i_boxed_3624_; size_t v_stop_boxed_3625_; lean_object* v_res_3626_; 
v_pu_boxed_3623_ = lean_unbox(v_pu_3610_);
v_i_boxed_3624_ = lean_unbox_usize(v_i_3613_);
lean_dec(v_i_3613_);
v_stop_boxed_3625_ = lean_unbox_usize(v_stop_3614_);
lean_dec(v_stop_3614_);
v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__10(v_pu_boxed_3623_, v_f_3611_, v_as_3612_, v_i_boxed_3624_, v_stop_boxed_3625_, v_b_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v_as_3612_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_3627_, lean_object* v_f_3628_, lean_object* v_c_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v_pu_boxed_3637_; lean_object* v_res_3638_; 
v_pu_boxed_3637_ = lean_unbox(v_pu_3627_);
v_res_3638_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_3637_, v_f_3628_, v_c_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec(v___y_3630_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_3639_, lean_object* v_f_3640_, lean_object* v_decl_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_params_3649_; lean_object* v_type_3650_; lean_object* v_value_3651_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v_params_3649_ = lean_ctor_get(v_decl_3641_, 2);
lean_inc_ref(v_params_3649_);
v_type_3650_ = lean_ctor_get(v_decl_3641_, 3);
lean_inc_ref(v_type_3650_);
v_value_3651_ = lean_ctor_get(v_decl_3641_, 4);
lean_inc_ref(v_value_3651_);
lean_dec_ref(v_decl_3641_);
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = lean_array_get_size(v_params_3649_);
v___x_3663_ = lean_nat_dec_lt(v___x_3661_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_dec_ref(v_params_3649_);
lean_inc_ref(v_f_3640_);
v___x_3664_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3640_, v_type_3650_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v___x_3665_; 
lean_dec_ref_known(v___x_3664_, 1);
v___x_3665_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3639_, v_f_3640_, v_value_3651_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
return v___x_3665_;
}
else
{
lean_dec_ref(v_value_3651_);
lean_dec_ref(v_f_3640_);
return v___x_3664_;
}
}
else
{
lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_nat_dec_le(v___x_3662_, v___x_3662_);
if (v___x_3667_ == 0)
{
if (v___x_3663_ == 0)
{
lean_dec_ref(v_params_3649_);
v___y_3653_ = v___y_3642_;
v___y_3654_ = v___y_3643_;
v___y_3655_ = v___y_3644_;
v___y_3656_ = v___y_3645_;
v___y_3657_ = v___y_3646_;
v___y_3658_ = v___y_3647_;
goto v___jp_3652_;
}
else
{
size_t v___x_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = ((size_t)0ULL);
v___x_3669_ = lean_usize_of_nat(v___x_3662_);
lean_inc_ref(v_f_3640_);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(v_pu_3639_, v_f_3640_, v_params_3649_, v___x_3668_, v___x_3669_, v___x_3666_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec_ref(v_params_3649_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_dec_ref_known(v___x_3670_, 1);
v___y_3653_ = v___y_3642_;
v___y_3654_ = v___y_3643_;
v___y_3655_ = v___y_3644_;
v___y_3656_ = v___y_3645_;
v___y_3657_ = v___y_3646_;
v___y_3658_ = v___y_3647_;
goto v___jp_3652_;
}
else
{
lean_dec_ref(v_value_3651_);
lean_dec_ref(v_type_3650_);
lean_dec_ref(v_f_3640_);
return v___x_3670_;
}
}
}
else
{
size_t v___x_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = ((size_t)0ULL);
v___x_3672_ = lean_usize_of_nat(v___x_3662_);
lean_inc_ref(v_f_3640_);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__7(v_pu_3639_, v_f_3640_, v_params_3649_, v___x_3671_, v___x_3672_, v___x_3666_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec_ref(v_params_3649_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_dec_ref_known(v___x_3673_, 1);
v___y_3653_ = v___y_3642_;
v___y_3654_ = v___y_3643_;
v___y_3655_ = v___y_3644_;
v___y_3656_ = v___y_3645_;
v___y_3657_ = v___y_3646_;
v___y_3658_ = v___y_3647_;
goto v___jp_3652_;
}
else
{
lean_dec_ref(v_value_3651_);
lean_dec_ref(v_type_3650_);
lean_dec_ref(v_f_3640_);
return v___x_3673_;
}
}
}
v___jp_3652_:
{
lean_object* v___x_3659_; 
lean_inc_ref(v_f_3640_);
v___x_3659_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3640_, v_type_3650_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; 
lean_dec_ref_known(v___x_3659_, 1);
v___x_3660_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3639_, v_f_3640_, v_value_3651_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
return v___x_3660_;
}
else
{
lean_dec_ref(v_value_3651_);
lean_dec_ref(v_f_3640_);
return v___x_3659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_3674_, lean_object* v_f_3675_, lean_object* v_decl_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
uint8_t v_pu_boxed_3684_; lean_object* v_res_3685_; 
v_pu_boxed_3684_ = lean_unbox(v_pu_3674_);
v_res_3685_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_3684_, v_f_3675_, v_decl_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec(v___y_3677_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg(lean_object* v_m_3686_, lean_object* v_query_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_3686_, v_query_3687_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_index_3689_; lean_object* v_key_3690_; lean_object* v_value_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
v_index_3689_ = lean_ctor_get(v___x_3688_, 0);
v_key_3690_ = lean_ctor_get(v___x_3688_, 1);
v_value_3691_ = lean_ctor_get(v___x_3688_, 2);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3688_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_value_3691_);
lean_inc(v_key_3690_);
lean_inc(v_index_3689_);
lean_dec(v___x_3688_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_index_3689_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_key_3690_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_value_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
else
{
lean_object* v___x_3699_; 
lean_dec(v___x_3688_);
v___x_3699_ = lean_box(1);
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_3700_, lean_object* v_query_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg(v_m_3700_, v_query_3701_);
lean_dec(v_query_3701_);
lean_dec_ref(v_m_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg(lean_object* v_m_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg(v_m_3703_, v_a_3704_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_value_3706_; lean_object* v___x_3707_; 
v_value_3706_ = lean_ctor_get(v___x_3705_, 2);
lean_inc(v_value_3706_);
lean_dec_ref_known(v___x_3705_, 3);
v___x_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3707_, 0, v_value_3706_);
return v___x_3707_;
}
else
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_box(0);
return v___x_3708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg___boxed(lean_object* v_m_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg(v_m_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_m_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__1(lean_object* v_msg_3712_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = lean_box(0);
v___x_3714_ = lean_panic_fn_borrowed(v___x_3713_, v_msg_3712_);
return v___x_3714_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3718_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__2));
v___x_3719_ = lean_unsigned_to_nat(12u);
v___x_3720_ = lean_unsigned_to_nat(672u);
v___x_3721_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__1));
v___x_3722_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__0));
v___x_3723_ = l_mkPanicMessageWithDecl(v___x_3722_, v___x_3721_, v___x_3720_, v___x_3719_, v___x_3718_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg(v_m_3724_, v_a_3725_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3);
v___x_3728_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__1(v___x_3727_);
return v___x_3728_;
}
else
{
lean_object* v_val_3729_; 
v_val_3729_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_val_3729_);
lean_dec_ref_known(v___x_3726_, 1);
return v_val_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3730_, v_a_3731_);
lean_dec(v_a_3731_);
lean_dec_ref(v_m_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v_i_3755_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_i_3780_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3801_; uint8_t v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = 0;
v___x_3846_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3734_))
{
case 0:
{
lean_object* v_decl_3847_; lean_object* v___x_3848_; 
v_decl_3847_ = lean_ctor_get(v_decl_3734_, 0);
lean_inc_ref(v_decl_3847_);
v___x_3848_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3845_, v___x_3846_, v_decl_3847_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3801_ = v___x_3848_;
goto v___jp_3800_;
}
case 1:
{
lean_object* v_decl_3849_; lean_object* v___x_3850_; 
v_decl_3849_ = lean_ctor_get(v_decl_3734_, 0);
lean_inc_ref(v_decl_3849_);
v___x_3850_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3845_, v___x_3846_, v_decl_3849_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3801_ = v___x_3850_;
goto v___jp_3800_;
}
case 2:
{
lean_object* v_decl_3851_; lean_object* v___x_3852_; 
v_decl_3851_ = lean_ctor_get(v_decl_3734_, 0);
lean_inc_ref(v_decl_3851_);
v___x_3852_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3845_, v___x_3846_, v_decl_3851_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3801_ = v___x_3852_;
goto v___jp_3800_;
}
case 3:
{
lean_object* v_fvarId_3853_; lean_object* v_y_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_fvarId_3853_ = lean_ctor_get(v_decl_3734_, 0);
v_y_3854_ = lean_ctor_get(v_decl_3734_, 2);
lean_inc(v_fvarId_3853_);
v___x_3855_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3853_, v_a_3735_);
lean_dec_ref(v___x_3855_);
lean_inc(v_y_3854_);
v___x_3856_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3846_, v_y_3854_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3801_ = v___x_3856_;
goto v___jp_3800_;
}
case 4:
{
lean_object* v_fvarId_3857_; lean_object* v_y_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_fvarId_3857_ = lean_ctor_get(v_decl_3734_, 0);
v_y_3858_ = lean_ctor_get(v_decl_3734_, 2);
lean_inc(v_fvarId_3857_);
v___x_3859_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3857_, v_a_3735_);
lean_dec_ref(v___x_3859_);
lean_inc(v_y_3858_);
v___x_3860_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3858_, v_a_3735_);
v___y_3801_ = v___x_3860_;
goto v___jp_3800_;
}
case 5:
{
lean_object* v_fvarId_3861_; lean_object* v_y_3862_; lean_object* v_ty_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_fvarId_3861_ = lean_ctor_get(v_decl_3734_, 0);
v_y_3862_ = lean_ctor_get(v_decl_3734_, 3);
v_ty_3863_ = lean_ctor_get(v_decl_3734_, 4);
lean_inc(v_fvarId_3861_);
v___x_3864_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3861_, v_a_3735_);
lean_dec_ref(v___x_3864_);
lean_inc(v_y_3862_);
v___x_3865_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3862_, v_a_3735_);
lean_dec_ref(v___x_3865_);
lean_inc_ref(v_ty_3863_);
v___x_3866_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3846_, v_ty_3863_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3801_ = v___x_3866_;
goto v___jp_3800_;
}
default: 
{
lean_object* v_fvarId_3867_; lean_object* v___x_3868_; 
v_fvarId_3867_ = lean_ctor_get(v_decl_3734_, 0);
lean_inc(v_fvarId_3867_);
v___x_3868_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3867_, v_a_3735_);
v___y_3801_ = v___x_3868_;
goto v___jp_3800_;
}
}
v___jp_3742_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___y_3744_);
lean_ctor_set(v___x_3746_, 1, v___y_3745_);
v___x_3747_ = lean_st_ref_put(v_a_3735_, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___y_3743_);
return v___x_3748_;
}
v___jp_3749_:
{
lean_object* v_size_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v_size_3756_ = lean_ctor_get(v___y_3750_, 0);
v___x_3757_ = lean_unsigned_to_nat(1u);
v___x_3758_ = lean_nat_add(v_size_3756_, v___x_3757_);
v___x_3759_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3750_, v___x_3758_, v_i_3755_, v___y_3751_, v___y_3753_);
lean_dec(v_i_3755_);
v___y_3743_ = v___y_3752_;
v___y_3744_ = v___y_3754_;
v___y_3745_ = v___x_3759_;
goto v___jp_3742_;
}
v___jp_3760_:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___y_3765_, v___y_3761_);
switch(lean_obj_tag(v___x_3766_))
{
case 0:
{
lean_object* v_index_3767_; lean_object* v_size_3768_; lean_object* v___x_3769_; 
v_index_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_index_3767_);
lean_dec_ref_known(v___x_3766_, 3);
v_size_3768_ = lean_ctor_get(v___y_3765_, 0);
lean_inc(v_size_3768_);
v___x_3769_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3765_, v_size_3768_, v_index_3767_, v___y_3761_, v___y_3763_);
lean_dec(v_index_3767_);
v___y_3743_ = v___y_3762_;
v___y_3744_ = v___y_3764_;
v___y_3745_ = v___x_3769_;
goto v___jp_3742_;
}
case 1:
{
lean_object* v_index_3770_; 
v_index_3770_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_index_3770_);
lean_dec_ref_known(v___x_3766_, 1);
v___y_3750_ = v___y_3765_;
v___y_3751_ = v___y_3761_;
v___y_3752_ = v___y_3762_;
v___y_3753_ = v___y_3763_;
v___y_3754_ = v___y_3764_;
v_i_3755_ = v_index_3770_;
goto v___jp_3749_;
}
default: 
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_unsigned_to_nat(0u);
v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3765_, v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_index_3773_; 
v_index_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_index_3773_);
lean_dec_ref_known(v___x_3772_, 1);
v___y_3750_ = v___y_3765_;
v___y_3751_ = v___y_3761_;
v___y_3752_ = v___y_3762_;
v___y_3753_ = v___y_3763_;
v___y_3754_ = v___y_3764_;
v_i_3755_ = v_index_3773_;
goto v___jp_3749_;
}
else
{
lean_dec(v___y_3763_);
lean_dec(v___y_3761_);
v___y_3743_ = v___y_3762_;
v___y_3744_ = v___y_3764_;
v___y_3745_ = v___y_3765_;
goto v___jp_3742_;
}
}
}
}
v___jp_3774_:
{
lean_object* v_size_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_size_3781_ = lean_ctor_get(v___y_3776_, 0);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_add(v_size_3781_, v___x_3782_);
v___x_3784_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3776_, v___x_3783_, v_i_3780_, v___y_3775_, v___y_3778_);
lean_dec(v_i_3780_);
v___y_3743_ = v___y_3777_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___x_3784_;
goto v___jp_3742_;
}
v___jp_3785_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v___y_3786_);
lean_dec_ref(v___y_3786_);
v___x_3792_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_3791_, v___y_3787_);
switch(lean_obj_tag(v___x_3792_))
{
case 0:
{
lean_object* v_index_3793_; lean_object* v_size_3794_; lean_object* v___x_3795_; 
v_index_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_index_3793_);
lean_dec_ref_known(v___x_3792_, 3);
v_size_3794_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_size_3794_);
v___x_3795_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3791_, v_size_3794_, v_index_3793_, v___y_3787_, v___y_3789_);
lean_dec(v_index_3793_);
v___y_3743_ = v___y_3788_;
v___y_3744_ = v___y_3790_;
v___y_3745_ = v___x_3795_;
goto v___jp_3742_;
}
case 1:
{
lean_object* v_index_3796_; 
v_index_3796_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_index_3796_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3775_ = v___y_3787_;
v___y_3776_ = v___x_3791_;
v___y_3777_ = v___y_3788_;
v___y_3778_ = v___y_3789_;
v___y_3779_ = v___y_3790_;
v_i_3780_ = v_index_3796_;
goto v___jp_3774_;
}
default: 
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_unsigned_to_nat(0u);
v___x_3798_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3791_, v___x_3797_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_index_3799_; 
v_index_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_index_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3775_ = v___y_3787_;
v___y_3776_ = v___x_3791_;
v___y_3777_ = v___y_3788_;
v___y_3778_ = v___y_3789_;
v___y_3779_ = v___y_3790_;
v_i_3780_ = v_index_3799_;
goto v___jp_3774_;
}
else
{
lean_dec(v___y_3789_);
lean_dec(v___y_3787_);
v___y_3743_ = v___y_3788_;
v___y_3744_ = v___y_3790_;
v___y_3745_ = v___x_3791_;
goto v___jp_3742_;
}
}
}
}
v___jp_3800_:
{
if (lean_obj_tag(v___y_3801_) == 0)
{
lean_object* v___x_3802_; lean_object* v_decision_3803_; lean_object* v_newArms_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref_known(v___y_3801_, 1);
v___x_3802_ = lean_st_ref_take(v_a_3735_);
v_decision_3803_ = lean_ctor_get(v___x_3802_, 0);
v_newArms_3804_ = lean_ctor_get(v___x_3802_, 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3806_ = v___x_3802_;
v_isShared_3807_ = v_isSharedCheck_3844_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_newArms_3804_);
lean_inc(v_decision_3803_);
lean_dec(v___x_3802_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3844_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3808_ = lean_box(0);
v___x_3809_ = lean_box(2);
v___x_3810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3804_, v___x_3809_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 1);
lean_ctor_set(v___x_3806_, 1, v___x_3810_);
lean_ctor_set(v___x_3806_, 0, v_decl_3734_);
v___x_3812_ = v___x_3806_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_decl_3734_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3804_, v___x_3809_);
switch(lean_obj_tag(v___x_3813_))
{
case 0:
{
lean_object* v_index_3814_; lean_object* v_size_3815_; lean_object* v___x_3816_; 
v_index_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_index_3814_);
lean_dec_ref_known(v___x_3813_, 3);
v_size_3815_ = lean_ctor_get(v_newArms_3804_, 0);
lean_inc(v_size_3815_);
v___x_3816_ = l_Std_DHashMap_Raw_setEntry___redArg(v_newArms_3804_, v_size_3815_, v_index_3814_, v___x_3809_, v___x_3812_);
lean_dec(v_index_3814_);
v___y_3743_ = v___x_3808_;
v___y_3744_ = v_decision_3803_;
v___y_3745_ = v___x_3816_;
goto v___jp_3742_;
}
case 1:
{
lean_object* v_index_3817_; lean_object* v_size_3818_; lean_object* v_keyArray_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_index_3817_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_index_3817_);
lean_dec_ref_known(v___x_3813_, 1);
v_size_3818_ = lean_ctor_get(v_newArms_3804_, 0);
v_keyArray_3819_ = lean_ctor_get(v_newArms_3804_, 1);
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_nat_add(v_size_3818_, v___x_3820_);
v___x_3822_ = lean_array_get_size(v_keyArray_3819_);
v___x_3823_ = lean_nat_dec_lt(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_dec(v___x_3821_);
lean_dec(v_index_3817_);
v___y_3786_ = v_newArms_3804_;
v___y_3787_ = v___x_3809_;
v___y_3788_ = v___x_3808_;
v___y_3789_ = v___x_3812_;
v___y_3790_ = v_decision_3803_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3824_ = lean_unsigned_to_nat(4u);
v___x_3825_ = lean_nat_mul(v___x_3821_, v___x_3824_);
v___x_3826_ = lean_unsigned_to_nat(3u);
v___x_3827_ = lean_nat_mul(v___x_3822_, v___x_3826_);
v___x_3828_ = lean_nat_dec_le(v___x_3825_, v___x_3827_);
lean_dec(v___x_3827_);
lean_dec(v___x_3825_);
if (v___x_3828_ == 0)
{
lean_dec(v___x_3821_);
lean_dec(v_index_3817_);
v___y_3786_ = v_newArms_3804_;
v___y_3787_ = v___x_3809_;
v___y_3788_ = v___x_3808_;
v___y_3789_ = v___x_3812_;
v___y_3790_ = v_decision_3803_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_DHashMap_Raw_setEntry___redArg(v_newArms_3804_, v___x_3821_, v_index_3817_, v___x_3809_, v___x_3812_);
lean_dec(v_index_3817_);
v___y_3743_ = v___x_3808_;
v___y_3744_ = v_decision_3803_;
v___y_3745_ = v___x_3829_;
goto v___jp_3742_;
}
}
}
default: 
{
lean_object* v_size_3830_; lean_object* v_keyArray_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_size_3830_ = lean_ctor_get(v_newArms_3804_, 0);
v_keyArray_3831_ = lean_ctor_get(v_newArms_3804_, 1);
v___x_3832_ = lean_unsigned_to_nat(1u);
v___x_3833_ = lean_nat_add(v_size_3830_, v___x_3832_);
v___x_3834_ = lean_array_get_size(v_keyArray_3831_);
v___x_3835_ = lean_nat_dec_lt(v___x_3833_, v___x_3834_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
lean_dec(v___x_3833_);
v___x_3836_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_newArms_3804_);
lean_dec_ref(v_newArms_3804_);
v___y_3761_ = v___x_3809_;
v___y_3762_ = v___x_3808_;
v___y_3763_ = v___x_3812_;
v___y_3764_ = v_decision_3803_;
v___y_3765_ = v___x_3836_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v___x_3837_ = lean_unsigned_to_nat(4u);
v___x_3838_ = lean_nat_mul(v___x_3833_, v___x_3837_);
lean_dec(v___x_3833_);
v___x_3839_ = lean_unsigned_to_nat(3u);
v___x_3840_ = lean_nat_mul(v___x_3834_, v___x_3839_);
v___x_3841_ = lean_nat_dec_le(v___x_3838_, v___x_3840_);
lean_dec(v___x_3840_);
lean_dec(v___x_3838_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_newArms_3804_);
lean_dec_ref(v_newArms_3804_);
v___y_3761_ = v___x_3809_;
v___y_3762_ = v___x_3808_;
v___y_3763_ = v___x_3812_;
v___y_3764_ = v_decision_3803_;
v___y_3765_ = v___x_3842_;
goto v___jp_3760_;
}
else
{
v___y_3761_ = v___x_3809_;
v___y_3762_ = v___x_3808_;
v___y_3763_ = v___x_3812_;
v___y_3764_ = v_decision_3803_;
v___y_3765_ = v_newArms_3804_;
goto v___jp_3760_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3734_);
return v___y_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec(v_a_3870_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3878_, lean_object* v_f_3879_, lean_object* v_arg_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3879_, v_arg_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3889_, lean_object* v_f_3890_, lean_object* v_arg_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v_pu_boxed_3899_; lean_object* v_res_3900_; 
v_pu_boxed_3899_ = lean_unbox(v_pu_3889_);
v_res_3900_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3899_, v_f_3890_, v_arg_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3892_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_00_u03b2_3901_, lean_object* v_m_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___redArg(v_m_3902_, v_a_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3905_, lean_object* v_m_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_00_u03b2_3905_, v_m_3906_, v_a_3907_);
lean_dec(v_a_3907_);
lean_dec_ref(v_m_3906_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_3909_, lean_object* v_f_3910_, lean_object* v_param_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___redArg(v_f_3910_, v_param_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_3920_, lean_object* v_f_3921_, lean_object* v_param_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
uint8_t v_pu_boxed_3930_; lean_object* v_res_3931_; 
v_pu_boxed_3930_ = lean_unbox(v_pu_3920_);
v_res_3931_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_3930_, v_f_3921_, v_param_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec(v___y_3923_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9(uint8_t v_pu_3932_, lean_object* v_alt_3933_, lean_object* v_f_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___redArg(v_alt_3933_, v_f_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9___boxed(lean_object* v_pu_3943_, lean_object* v_alt_3944_, lean_object* v_f_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
uint8_t v_pu_boxed_3953_; lean_object* v_res_3954_; 
v_pu_boxed_3953_ = lean_unbox(v_pu_3943_);
v_res_3954_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_spec__9(v_pu_boxed_3953_, v_alt_3944_, v_f_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec(v___y_3946_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3955_, lean_object* v_m_3956_, lean_object* v_query_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___redArg(v_m_3956_, v_query_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3959_, lean_object* v_m_3960_, lean_object* v_query_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v_00_u03b2_3959_, v_m_3960_, v_query_3961_);
lean_dec(v_query_3961_);
lean_dec_ref(v_m_3960_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3963_, lean_object* v_arm_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___y_3968_; lean_object* v_newArms_3969_; lean_object* v___y_3970_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v_i_3984_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v_i_4008_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___x_4026_; lean_object* v_decision_4063_; lean_object* v___x_4064_; 
v___x_4026_ = lean_st_ref_get(v_a_3965_);
v_decision_4063_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_decision_4063_);
lean_dec(v___x_4026_);
v___x_4064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_4063_, v_fvar_3963_);
lean_dec_ref(v_decision_4063_);
if (lean_obj_tag(v___x_4064_) == 1)
{
lean_object* v_val_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4157_; 
v_val_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4157_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_val_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4157_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = lean_box(3);
v___x_4070_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_4065_, v___x_4069_);
if (v___x_4070_ == 0)
{
uint8_t v___x_4071_; 
v___x_4071_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_4065_, v_arm_3964_);
lean_dec(v_arm_3964_);
lean_dec(v_val_4065_);
if (v___x_4071_ == 0)
{
lean_del_object(v___x_4067_);
goto v___jp_4027_;
}
else
{
if (v___x_4070_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4074_; 
lean_dec(v_fvar_3963_);
v___x_4072_ = lean_box(0);
if (v_isShared_4068_ == 0)
{
lean_ctor_set_tag(v___x_4067_, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4072_);
v___x_4074_ = v___x_4067_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
else
{
lean_del_object(v___x_4067_);
goto v___jp_4027_;
}
}
}
else
{
lean_object* v___x_4076_; lean_object* v_decision_4077_; lean_object* v_newArms_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4156_; 
lean_dec(v_val_4065_);
v___x_4076_ = lean_st_ref_take(v_a_3965_);
v_decision_4077_ = lean_ctor_get(v___x_4076_, 0);
v_newArms_4078_ = lean_ctor_get(v___x_4076_, 1);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4080_ = v___x_4076_;
v_isShared_4081_ = v_isSharedCheck_4156_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_newArms_4078_);
lean_inc(v_decision_4077_);
lean_dec(v___x_4076_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4156_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___y_4084_; lean_object* v___y_4093_; lean_object* v_i_4094_; lean_object* v___y_4110_; lean_object* v_i_4111_; lean_object* v___y_4117_; lean_object* v___x_4126_; 
v___x_4082_ = lean_box(0);
v___x_4126_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_decision_4077_, v_fvar_3963_);
switch(lean_obj_tag(v___x_4126_))
{
case 0:
{
lean_object* v_index_4127_; lean_object* v_size_4128_; lean_object* v___x_4129_; 
v_index_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_index_4127_);
lean_dec_ref_known(v___x_4126_, 3);
v_size_4128_ = lean_ctor_get(v_decision_4077_, 0);
lean_inc(v_size_4128_);
v___x_4129_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decision_4077_, v_size_4128_, v_index_4127_, v_fvar_3963_, v_arm_3964_);
lean_dec(v_index_4127_);
v___y_4084_ = v___x_4129_;
goto v___jp_4083_;
}
case 1:
{
lean_object* v_index_4130_; lean_object* v_size_4131_; lean_object* v_keyArray_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v_index_4130_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_index_4130_);
lean_dec_ref_known(v___x_4126_, 1);
v_size_4131_ = lean_ctor_get(v_decision_4077_, 0);
v_keyArray_4132_ = lean_ctor_get(v_decision_4077_, 1);
v___x_4133_ = lean_unsigned_to_nat(1u);
v___x_4134_ = lean_nat_add(v_size_4131_, v___x_4133_);
v___x_4135_ = lean_array_get_size(v_keyArray_4132_);
v___x_4136_ = lean_nat_dec_lt(v___x_4134_, v___x_4135_);
if (v___x_4136_ == 0)
{
lean_dec(v___x_4134_);
lean_dec(v_index_4130_);
goto v___jp_4099_;
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4137_ = lean_unsigned_to_nat(4u);
v___x_4138_ = lean_nat_mul(v___x_4134_, v___x_4137_);
v___x_4139_ = lean_unsigned_to_nat(3u);
v___x_4140_ = lean_nat_mul(v___x_4135_, v___x_4139_);
v___x_4141_ = lean_nat_dec_le(v___x_4138_, v___x_4140_);
lean_dec(v___x_4140_);
lean_dec(v___x_4138_);
if (v___x_4141_ == 0)
{
lean_dec(v___x_4134_);
lean_dec(v_index_4130_);
goto v___jp_4099_;
}
else
{
lean_object* v___x_4142_; 
v___x_4142_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decision_4077_, v___x_4134_, v_index_4130_, v_fvar_3963_, v_arm_3964_);
lean_dec(v_index_4130_);
v___y_4084_ = v___x_4142_;
goto v___jp_4083_;
}
}
}
default: 
{
lean_object* v_size_4143_; lean_object* v_keyArray_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; uint8_t v___x_4148_; 
v_size_4143_ = lean_ctor_get(v_decision_4077_, 0);
v_keyArray_4144_ = lean_ctor_get(v_decision_4077_, 1);
v___x_4145_ = lean_unsigned_to_nat(1u);
v___x_4146_ = lean_nat_add(v_size_4143_, v___x_4145_);
v___x_4147_ = lean_array_get_size(v_keyArray_4144_);
v___x_4148_ = lean_nat_dec_lt(v___x_4146_, v___x_4147_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; 
lean_dec(v___x_4146_);
v___x_4149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_4077_);
lean_dec_ref(v_decision_4077_);
v___y_4117_ = v___x_4149_;
goto v___jp_4116_;
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v___x_4150_ = lean_unsigned_to_nat(4u);
v___x_4151_ = lean_nat_mul(v___x_4146_, v___x_4150_);
lean_dec(v___x_4146_);
v___x_4152_ = lean_unsigned_to_nat(3u);
v___x_4153_ = lean_nat_mul(v___x_4147_, v___x_4152_);
v___x_4154_ = lean_nat_dec_le(v___x_4151_, v___x_4153_);
lean_dec(v___x_4153_);
lean_dec(v___x_4151_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_4077_);
lean_dec_ref(v_decision_4077_);
v___y_4117_ = v___x_4155_;
goto v___jp_4116_;
}
else
{
v___y_4117_ = v_decision_4077_;
goto v___jp_4116_;
}
}
}
}
v___jp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___y_4084_);
v___x_4086_ = v___x_4080_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___y_4084_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_newArms_4078_);
v___x_4086_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = lean_st_ref_put(v_a_3965_, v___x_4086_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set_tag(v___x_4067_, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4082_);
v___x_4089_ = v___x_4067_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4082_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
v___jp_4092_:
{
lean_object* v_size_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_size_4095_ = lean_ctor_get(v___y_4093_, 0);
v___x_4096_ = lean_unsigned_to_nat(1u);
v___x_4097_ = lean_nat_add(v_size_4095_, v___x_4096_);
v___x_4098_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4093_, v___x_4097_, v_i_4094_, v_fvar_3963_, v_arm_3964_);
lean_dec(v_i_4094_);
v___y_4084_ = v___x_4098_;
goto v___jp_4083_;
}
v___jp_4099_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_4077_);
lean_dec_ref(v_decision_4077_);
v___x_4101_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_4100_, v_fvar_3963_);
switch(lean_obj_tag(v___x_4101_))
{
case 0:
{
lean_object* v_index_4102_; lean_object* v_size_4103_; lean_object* v___x_4104_; 
v_index_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_index_4102_);
lean_dec_ref_known(v___x_4101_, 3);
v_size_4103_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_size_4103_);
v___x_4104_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4100_, v_size_4103_, v_index_4102_, v_fvar_3963_, v_arm_3964_);
lean_dec(v_index_4102_);
v___y_4084_ = v___x_4104_;
goto v___jp_4083_;
}
case 1:
{
lean_object* v_index_4105_; 
v_index_4105_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_index_4105_);
lean_dec_ref_known(v___x_4101_, 1);
v___y_4093_ = v___x_4100_;
v_i_4094_ = v_index_4105_;
goto v___jp_4092_;
}
default: 
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4100_, v___x_4106_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_index_4108_; 
v_index_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_index_4108_);
lean_dec_ref_known(v___x_4107_, 1);
v___y_4093_ = v___x_4100_;
v_i_4094_ = v_index_4108_;
goto v___jp_4092_;
}
else
{
lean_dec(v_arm_3964_);
lean_dec(v_fvar_3963_);
v___y_4084_ = v___x_4100_;
goto v___jp_4083_;
}
}
}
}
v___jp_4109_:
{
lean_object* v_size_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v_size_4112_ = lean_ctor_get(v___y_4110_, 0);
v___x_4113_ = lean_unsigned_to_nat(1u);
v___x_4114_ = lean_nat_add(v_size_4112_, v___x_4113_);
v___x_4115_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4110_, v___x_4114_, v_i_4111_, v_fvar_3963_, v_arm_3964_);
lean_dec(v_i_4111_);
v___y_4084_ = v___x_4115_;
goto v___jp_4083_;
}
v___jp_4116_:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_4117_, v_fvar_3963_);
switch(lean_obj_tag(v___x_4118_))
{
case 0:
{
lean_object* v_index_4119_; lean_object* v_size_4120_; lean_object* v___x_4121_; 
v_index_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_index_4119_);
lean_dec_ref_known(v___x_4118_, 3);
v_size_4120_ = lean_ctor_get(v___y_4117_, 0);
lean_inc(v_size_4120_);
v___x_4121_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4117_, v_size_4120_, v_index_4119_, v_fvar_3963_, v_arm_3964_);
lean_dec(v_index_4119_);
v___y_4084_ = v___x_4121_;
goto v___jp_4083_;
}
case 1:
{
lean_object* v_index_4122_; 
v_index_4122_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_index_4122_);
lean_dec_ref_known(v___x_4118_, 1);
v___y_4110_ = v___y_4117_;
v_i_4111_ = v_index_4122_;
goto v___jp_4109_;
}
default: 
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = lean_unsigned_to_nat(0u);
v___x_4124_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4117_, v___x_4123_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_index_4125_; 
v_index_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_index_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v___y_4110_ = v___y_4117_;
v_i_4111_ = v_index_4125_;
goto v___jp_4109_;
}
else
{
lean_dec(v_arm_3964_);
lean_dec(v_fvar_3963_);
v___y_4084_ = v___y_4117_;
goto v___jp_4083_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_dec(v___x_4064_);
lean_dec(v_arm_3964_);
lean_dec(v_fvar_3963_);
v___x_4158_ = lean_box(0);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
return v___x_4159_;
}
v___jp_3967_:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___y_3970_);
lean_ctor_set(v___x_3971_, 1, v_newArms_3969_);
v___x_3972_ = lean_st_ref_put(v_a_3965_, v___x_3971_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___y_3968_);
return v___x_3973_;
}
v___jp_3974_:
{
lean_object* v_newArms_3978_; 
v_newArms_3978_ = lean_ctor_get(v___y_3976_, 1);
lean_inc_ref(v_newArms_3978_);
lean_dec_ref(v___y_3976_);
v___y_3968_ = v___y_3975_;
v_newArms_3969_ = v_newArms_3978_;
v___y_3970_ = v___y_3977_;
goto v___jp_3967_;
}
v___jp_3979_:
{
lean_object* v_size_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_size_3985_ = lean_ctor_get(v___y_3982_, 0);
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = lean_nat_add(v_size_3985_, v___x_3986_);
v___x_3988_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3982_, v___x_3987_, v_i_3984_, v_fvar_3963_, v___y_3981_);
lean_dec(v_i_3984_);
v___y_3975_ = v___y_3980_;
v___y_3976_ = v___y_3983_;
v___y_3977_ = v___x_3988_;
goto v___jp_3974_;
}
v___jp_3989_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v___y_3992_);
lean_dec_ref(v___y_3992_);
v___x_3995_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_3994_, v_fvar_3963_);
switch(lean_obj_tag(v___x_3995_))
{
case 0:
{
lean_object* v_index_3996_; lean_object* v_size_3997_; lean_object* v___x_3998_; 
v_index_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_index_3996_);
lean_dec_ref_known(v___x_3995_, 3);
v_size_3997_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_size_3997_);
v___x_3998_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3994_, v_size_3997_, v_index_3996_, v_fvar_3963_, v___y_3991_);
lean_dec(v_index_3996_);
v___y_3975_ = v___y_3990_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_3998_;
goto v___jp_3974_;
}
case 1:
{
lean_object* v_index_3999_; 
v_index_3999_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_index_3999_);
lean_dec_ref_known(v___x_3995_, 1);
v___y_3980_ = v___y_3990_;
v___y_3981_ = v___y_3991_;
v___y_3982_ = v___x_3994_;
v___y_3983_ = v___y_3993_;
v_i_3984_ = v_index_3999_;
goto v___jp_3979_;
}
default: 
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_unsigned_to_nat(0u);
v___x_4001_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3994_, v___x_4000_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_index_4002_; 
v_index_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_index_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v___y_3980_ = v___y_3990_;
v___y_3981_ = v___y_3991_;
v___y_3982_ = v___x_3994_;
v___y_3983_ = v___y_3993_;
v_i_3984_ = v_index_4002_;
goto v___jp_3979_;
}
else
{
lean_dec(v___y_3991_);
lean_dec(v_fvar_3963_);
v___y_3975_ = v___y_3990_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_3994_;
goto v___jp_3974_;
}
}
}
}
v___jp_4003_:
{
lean_object* v_size_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_size_4009_ = lean_ctor_get(v___y_4005_, 0);
v___x_4010_ = lean_unsigned_to_nat(1u);
v___x_4011_ = lean_nat_add(v_size_4009_, v___x_4010_);
v___x_4012_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4005_, v___x_4011_, v_i_4008_, v_fvar_3963_, v___y_4006_);
lean_dec(v_i_4008_);
v___y_3975_ = v___y_4004_;
v___y_3976_ = v___y_4007_;
v___y_3977_ = v___x_4012_;
goto v___jp_3974_;
}
v___jp_4013_:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___y_4017_, v_fvar_3963_);
switch(lean_obj_tag(v___x_4018_))
{
case 0:
{
lean_object* v_index_4019_; lean_object* v_size_4020_; lean_object* v___x_4021_; 
v_index_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_index_4019_);
lean_dec_ref_known(v___x_4018_, 3);
v_size_4020_ = lean_ctor_get(v___y_4017_, 0);
lean_inc(v_size_4020_);
v___x_4021_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4017_, v_size_4020_, v_index_4019_, v_fvar_3963_, v___y_4015_);
lean_dec(v_index_4019_);
v___y_3975_ = v___y_4014_;
v___y_3976_ = v___y_4016_;
v___y_3977_ = v___x_4021_;
goto v___jp_3974_;
}
case 1:
{
lean_object* v_index_4022_; 
v_index_4022_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_index_4022_);
lean_dec_ref_known(v___x_4018_, 1);
v___y_4004_ = v___y_4014_;
v___y_4005_ = v___y_4017_;
v___y_4006_ = v___y_4015_;
v___y_4007_ = v___y_4016_;
v_i_4008_ = v_index_4022_;
goto v___jp_4003_;
}
default: 
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_unsigned_to_nat(0u);
v___x_4024_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4017_, v___x_4023_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_index_4025_; 
v_index_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_index_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v___y_4004_ = v___y_4014_;
v___y_4005_ = v___y_4017_;
v___y_4006_ = v___y_4015_;
v___y_4007_ = v___y_4016_;
v_i_4008_ = v_index_4025_;
goto v___jp_4003_;
}
else
{
lean_dec(v___y_4015_);
lean_dec(v_fvar_3963_);
v___y_3975_ = v___y_4014_;
v___y_3976_ = v___y_4016_;
v___y_3977_ = v___y_4017_;
goto v___jp_3974_;
}
}
}
}
v___jp_4027_:
{
lean_object* v___x_4028_; lean_object* v_decision_4029_; lean_object* v_newArms_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4028_ = lean_st_ref_take(v_a_3965_);
v_decision_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc_ref(v_decision_4029_);
v_newArms_4030_ = lean_ctor_get(v___x_4028_, 1);
lean_inc_ref(v_newArms_4030_);
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_box(2);
v___x_4033_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_decision_4029_, v_fvar_3963_);
switch(lean_obj_tag(v___x_4033_))
{
case 0:
{
lean_object* v_index_4034_; lean_object* v_size_4035_; lean_object* v___x_4036_; 
lean_dec(v___x_4028_);
v_index_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_index_4034_);
lean_dec_ref_known(v___x_4033_, 3);
v_size_4035_ = lean_ctor_get(v_decision_4029_, 0);
lean_inc(v_size_4035_);
v___x_4036_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decision_4029_, v_size_4035_, v_index_4034_, v_fvar_3963_, v___x_4032_);
lean_dec(v_index_4034_);
v___y_3968_ = v___x_4031_;
v_newArms_3969_ = v_newArms_4030_;
v___y_3970_ = v___x_4036_;
goto v___jp_3967_;
}
case 1:
{
lean_object* v_index_4037_; lean_object* v_size_4038_; lean_object* v_keyArray_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; 
v_index_4037_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_index_4037_);
lean_dec_ref_known(v___x_4033_, 1);
v_size_4038_ = lean_ctor_get(v_decision_4029_, 0);
v_keyArray_4039_ = lean_ctor_get(v_decision_4029_, 1);
v___x_4040_ = lean_unsigned_to_nat(1u);
v___x_4041_ = lean_nat_add(v_size_4038_, v___x_4040_);
v___x_4042_ = lean_array_get_size(v_keyArray_4039_);
v___x_4043_ = lean_nat_dec_lt(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_dec(v___x_4041_);
lean_dec(v_index_4037_);
lean_dec_ref(v_newArms_4030_);
v___y_3990_ = v___x_4031_;
v___y_3991_ = v___x_4032_;
v___y_3992_ = v_decision_4029_;
v___y_3993_ = v___x_4028_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; 
v___x_4044_ = lean_unsigned_to_nat(4u);
v___x_4045_ = lean_nat_mul(v___x_4041_, v___x_4044_);
v___x_4046_ = lean_unsigned_to_nat(3u);
v___x_4047_ = lean_nat_mul(v___x_4042_, v___x_4046_);
v___x_4048_ = lean_nat_dec_le(v___x_4045_, v___x_4047_);
lean_dec(v___x_4047_);
lean_dec(v___x_4045_);
if (v___x_4048_ == 0)
{
lean_dec(v___x_4041_);
lean_dec(v_index_4037_);
lean_dec_ref(v_newArms_4030_);
v___y_3990_ = v___x_4031_;
v___y_3991_ = v___x_4032_;
v___y_3992_ = v_decision_4029_;
v___y_3993_ = v___x_4028_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4049_; 
lean_dec(v___x_4028_);
v___x_4049_ = l_Std_DHashMap_Raw_setEntry___redArg(v_decision_4029_, v___x_4041_, v_index_4037_, v_fvar_3963_, v___x_4032_);
lean_dec(v_index_4037_);
v___y_3968_ = v___x_4031_;
v_newArms_3969_ = v_newArms_4030_;
v___y_3970_ = v___x_4049_;
goto v___jp_3967_;
}
}
}
default: 
{
lean_object* v_size_4050_; lean_object* v_keyArray_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
lean_dec_ref(v_newArms_4030_);
v_size_4050_ = lean_ctor_get(v_decision_4029_, 0);
v_keyArray_4051_ = lean_ctor_get(v_decision_4029_, 1);
v___x_4052_ = lean_unsigned_to_nat(1u);
v___x_4053_ = lean_nat_add(v_size_4050_, v___x_4052_);
v___x_4054_ = lean_array_get_size(v_keyArray_4051_);
v___x_4055_ = lean_nat_dec_lt(v___x_4053_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; 
lean_dec(v___x_4053_);
v___x_4056_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_4029_);
lean_dec_ref(v_decision_4029_);
v___y_4014_ = v___x_4031_;
v___y_4015_ = v___x_4032_;
v___y_4016_ = v___x_4028_;
v___y_4017_ = v___x_4056_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4057_ = lean_unsigned_to_nat(4u);
v___x_4058_ = lean_nat_mul(v___x_4053_, v___x_4057_);
lean_dec(v___x_4053_);
v___x_4059_ = lean_unsigned_to_nat(3u);
v___x_4060_ = lean_nat_mul(v___x_4054_, v___x_4059_);
v___x_4061_ = lean_nat_dec_le(v___x_4058_, v___x_4060_);
lean_dec(v___x_4060_);
lean_dec(v___x_4058_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__2___redArg(v_decision_4029_);
lean_dec_ref(v_decision_4029_);
v___y_4014_ = v___x_4031_;
v___y_4015_ = v___x_4032_;
v___y_4016_ = v___x_4028_;
v___y_4017_ = v___x_4062_;
goto v___jp_4013_;
}
else
{
v___y_4014_ = v___x_4031_;
v___y_4015_ = v___x_4032_;
v___y_4016_ = v___x_4028_;
v___y_4017_ = v_decision_4029_;
goto v___jp_4013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_4160_, lean_object* v_arm_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_4160_, v_arm_4161_, v_a_4162_);
lean_dec(v_a_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_4165_, lean_object* v_arm_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_4165_, v_arm_4166_, v_a_4167_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_4175_, lean_object* v_arm_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_4175_, v_arm_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec(v_a_4177_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_4185_, lean_object* v_x_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_4186_, v___x_4185_, v___y_4187_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_4195_, lean_object* v_x_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_4195_, v_x_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec(v___y_4197_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_msg_4205_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_4207_ = lean_panic_fn_borrowed(v___x_4206_, v_msg_4205_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_4208_, v_a_4209_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___closed__3);
v___x_4212_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v___x_4211_);
return v___x_4212_;
}
else
{
lean_object* v_val_4213_; 
v_val_4213_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_val_4213_);
lean_dec_ref_known(v___x_4210_, 1);
return v_val_4213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_m_4214_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___x_4232_; lean_object* v_decision_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v_i_4242_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v_i_4265_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4285_; lean_object* v___f_4328_; 
v___x_4232_ = lean_st_ref_get(v_a_4218_);
v_decision_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc_ref(v_decision_4233_);
lean_dec(v___x_4232_);
v___x_4234_ = 0;
v___x_4235_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_4217_);
v___x_4236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_4233_, v___x_4235_);
lean_dec(v___x_4235_);
lean_dec_ref(v_decision_4233_);
lean_inc(v___x_4236_);
v___f_4328_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4328_, 0, v___x_4236_);
switch(lean_obj_tag(v_decl_4217_))
{
case 0:
{
lean_object* v_decl_4329_; lean_object* v___x_4330_; 
v_decl_4329_ = lean_ctor_get(v_decl_4217_, 0);
lean_inc_ref(v_decl_4329_);
v___x_4330_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_4234_, v___f_4328_, v_decl_4329_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
v___y_4285_ = v___x_4330_;
goto v___jp_4284_;
}
case 1:
{
lean_object* v_decl_4331_; lean_object* v___x_4332_; 
v_decl_4331_ = lean_ctor_get(v_decl_4217_, 0);
lean_inc_ref(v_decl_4331_);
v___x_4332_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_4234_, v___f_4328_, v_decl_4331_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
v___y_4285_ = v___x_4332_;
goto v___jp_4284_;
}
case 2:
{
lean_object* v_decl_4333_; lean_object* v___x_4334_; 
v_decl_4333_ = lean_ctor_get(v_decl_4217_, 0);
lean_inc_ref(v_decl_4333_);
v___x_4334_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_4234_, v___f_4328_, v_decl_4333_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
v___y_4285_ = v___x_4334_;
goto v___jp_4284_;
}
case 3:
{
lean_object* v_fvarId_4335_; lean_object* v_y_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_fvarId_4335_ = lean_ctor_get(v_decl_4217_, 0);
v_y_4336_ = lean_ctor_get(v_decl_4217_, 2);
lean_inc(v___x_4236_);
lean_inc(v_fvarId_4335_);
v___x_4337_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_4335_, v___x_4236_, v_a_4218_);
lean_dec_ref(v___x_4337_);
lean_inc(v_y_4336_);
v___x_4338_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_4328_, v_y_4336_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
v___y_4285_ = v___x_4338_;
goto v___jp_4284_;
}
case 4:
{
lean_object* v_fvarId_4339_; lean_object* v_y_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
lean_dec_ref(v___f_4328_);
v_fvarId_4339_ = lean_ctor_get(v_decl_4217_, 0);
v_y_4340_ = lean_ctor_get(v_decl_4217_, 2);
lean_inc_n(v___x_4236_, 2);
lean_inc(v_fvarId_4339_);
v___x_4341_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_4339_, v___x_4236_, v_a_4218_);
lean_dec_ref(v___x_4341_);
lean_inc(v_y_4340_);
v___x_4342_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_4340_, v___x_4236_, v_a_4218_);
v___y_4285_ = v___x_4342_;
goto v___jp_4284_;
}
case 5:
{
lean_object* v_fvarId_4343_; lean_object* v_y_4344_; lean_object* v_ty_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v_fvarId_4343_ = lean_ctor_get(v_decl_4217_, 0);
v_y_4344_ = lean_ctor_get(v_decl_4217_, 3);
v_ty_4345_ = lean_ctor_get(v_decl_4217_, 4);
lean_inc_n(v___x_4236_, 2);
lean_inc(v_fvarId_4343_);
v___x_4346_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_4343_, v___x_4236_, v_a_4218_);
lean_dec_ref(v___x_4346_);
lean_inc(v_y_4344_);
v___x_4347_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_4344_, v___x_4236_, v_a_4218_);
lean_dec_ref(v___x_4347_);
lean_inc_ref(v_ty_4345_);
v___x_4348_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_4328_, v_ty_4345_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
v___y_4285_ = v___x_4348_;
goto v___jp_4284_;
}
default: 
{
lean_object* v_fvarId_4349_; lean_object* v___x_4350_; 
lean_dec_ref(v___f_4328_);
v_fvarId_4349_ = lean_ctor_get(v_decl_4217_, 0);
lean_inc(v___x_4236_);
lean_inc(v_fvarId_4349_);
v___x_4350_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_4349_, v___x_4236_, v_a_4218_);
v___y_4285_ = v___x_4350_;
goto v___jp_4284_;
}
}
v___jp_4225_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___y_4226_);
lean_ctor_set(v___x_4229_, 1, v___y_4228_);
v___x_4230_ = lean_st_ref_put(v_a_4218_, v___x_4229_);
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___y_4227_);
return v___x_4231_;
}
v___jp_4237_:
{
lean_object* v_size_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_size_4243_ = lean_ctor_get(v___y_4240_, 0);
v___x_4244_ = lean_unsigned_to_nat(1u);
v___x_4245_ = lean_nat_add(v_size_4243_, v___x_4244_);
v___x_4246_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4240_, v___x_4245_, v_i_4242_, v___x_4236_, v___y_4238_);
lean_dec(v_i_4242_);
v___y_4226_ = v___y_4239_;
v___y_4227_ = v___y_4241_;
v___y_4228_ = v___x_4246_;
goto v___jp_4225_;
}
v___jp_4247_:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___y_4251_, v___x_4236_);
switch(lean_obj_tag(v___x_4252_))
{
case 0:
{
lean_object* v_index_4253_; lean_object* v_size_4254_; lean_object* v___x_4255_; 
v_index_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_index_4253_);
lean_dec_ref_known(v___x_4252_, 3);
v_size_4254_ = lean_ctor_get(v___y_4251_, 0);
lean_inc(v_size_4254_);
v___x_4255_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4251_, v_size_4254_, v_index_4253_, v___x_4236_, v___y_4248_);
lean_dec(v_index_4253_);
v___y_4226_ = v___y_4249_;
v___y_4227_ = v___y_4250_;
v___y_4228_ = v___x_4255_;
goto v___jp_4225_;
}
case 1:
{
lean_object* v_index_4256_; 
v_index_4256_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_index_4256_);
lean_dec_ref_known(v___x_4252_, 1);
v___y_4238_ = v___y_4248_;
v___y_4239_ = v___y_4249_;
v___y_4240_ = v___y_4251_;
v___y_4241_ = v___y_4250_;
v_i_4242_ = v_index_4256_;
goto v___jp_4237_;
}
default: 
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4257_ = lean_unsigned_to_nat(0u);
v___x_4258_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4251_, v___x_4257_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_index_4259_; 
v_index_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_index_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v___y_4238_ = v___y_4248_;
v___y_4239_ = v___y_4249_;
v___y_4240_ = v___y_4251_;
v___y_4241_ = v___y_4250_;
v_i_4242_ = v_index_4259_;
goto v___jp_4237_;
}
else
{
lean_dec(v___y_4248_);
lean_dec(v___x_4236_);
v___y_4226_ = v___y_4249_;
v___y_4227_ = v___y_4250_;
v___y_4228_ = v___y_4251_;
goto v___jp_4225_;
}
}
}
}
v___jp_4260_:
{
lean_object* v_size_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_size_4266_ = lean_ctor_get(v___y_4263_, 0);
v___x_4267_ = lean_unsigned_to_nat(1u);
v___x_4268_ = lean_nat_add(v_size_4266_, v___x_4267_);
v___x_4269_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4263_, v___x_4268_, v_i_4265_, v___x_4236_, v___y_4261_);
lean_dec(v_i_4265_);
v___y_4226_ = v___y_4262_;
v___y_4227_ = v___y_4264_;
v___y_4228_ = v___x_4269_;
goto v___jp_4225_;
}
v___jp_4270_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v___y_4273_);
lean_dec_ref(v___y_4273_);
v___x_4276_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_4275_, v___x_4236_);
switch(lean_obj_tag(v___x_4276_))
{
case 0:
{
lean_object* v_index_4277_; lean_object* v_size_4278_; lean_object* v___x_4279_; 
v_index_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_index_4277_);
lean_dec_ref_known(v___x_4276_, 3);
v_size_4278_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_size_4278_);
v___x_4279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4275_, v_size_4278_, v_index_4277_, v___x_4236_, v___y_4271_);
lean_dec(v_index_4277_);
v___y_4226_ = v___y_4272_;
v___y_4227_ = v___y_4274_;
v___y_4228_ = v___x_4279_;
goto v___jp_4225_;
}
case 1:
{
lean_object* v_index_4280_; 
v_index_4280_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_index_4280_);
lean_dec_ref_known(v___x_4276_, 1);
v___y_4261_ = v___y_4271_;
v___y_4262_ = v___y_4272_;
v___y_4263_ = v___x_4275_;
v___y_4264_ = v___y_4274_;
v_i_4265_ = v_index_4280_;
goto v___jp_4260_;
}
default: 
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_unsigned_to_nat(0u);
v___x_4282_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4275_, v___x_4281_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_index_4283_; 
v_index_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_index_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___y_4261_ = v___y_4271_;
v___y_4262_ = v___y_4272_;
v___y_4263_ = v___x_4275_;
v___y_4264_ = v___y_4274_;
v_i_4265_ = v_index_4283_;
goto v___jp_4260_;
}
else
{
lean_dec(v___y_4271_);
lean_dec(v___x_4236_);
v___y_4226_ = v___y_4272_;
v___y_4227_ = v___y_4274_;
v___y_4228_ = v___x_4275_;
goto v___jp_4225_;
}
}
}
}
v___jp_4284_:
{
if (lean_obj_tag(v___y_4285_) == 0)
{
lean_object* v___x_4286_; lean_object* v_decision_4287_; lean_object* v_newArms_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref_known(v___y_4285_, 1);
v___x_4286_ = lean_st_ref_take(v_a_4218_);
v_decision_4287_ = lean_ctor_get(v___x_4286_, 0);
v_newArms_4288_ = lean_ctor_get(v___x_4286_, 1);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4290_ = v___x_4286_;
v_isShared_4291_ = v_isSharedCheck_4327_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_newArms_4288_);
lean_inc(v_decision_4287_);
lean_dec(v___x_4286_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4327_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4292_ = lean_box(0);
v___x_4293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_4288_, v___x_4236_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 1);
lean_ctor_set(v___x_4290_, 1, v___x_4293_);
lean_ctor_set(v___x_4290_, 0, v_decl_4217_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_decl_4217_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_4288_, v___x_4236_);
switch(lean_obj_tag(v___x_4296_))
{
case 0:
{
lean_object* v_index_4297_; lean_object* v_size_4298_; lean_object* v___x_4299_; 
v_index_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_index_4297_);
lean_dec_ref_known(v___x_4296_, 3);
v_size_4298_ = lean_ctor_get(v_newArms_4288_, 0);
lean_inc(v_size_4298_);
v___x_4299_ = l_Std_DHashMap_Raw_setEntry___redArg(v_newArms_4288_, v_size_4298_, v_index_4297_, v___x_4236_, v___x_4295_);
lean_dec(v_index_4297_);
v___y_4226_ = v_decision_4287_;
v___y_4227_ = v___x_4292_;
v___y_4228_ = v___x_4299_;
goto v___jp_4225_;
}
case 1:
{
lean_object* v_index_4300_; lean_object* v_size_4301_; lean_object* v_keyArray_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v_index_4300_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_index_4300_);
lean_dec_ref_known(v___x_4296_, 1);
v_size_4301_ = lean_ctor_get(v_newArms_4288_, 0);
v_keyArray_4302_ = lean_ctor_get(v_newArms_4288_, 1);
v___x_4303_ = lean_unsigned_to_nat(1u);
v___x_4304_ = lean_nat_add(v_size_4301_, v___x_4303_);
v___x_4305_ = lean_array_get_size(v_keyArray_4302_);
v___x_4306_ = lean_nat_dec_lt(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec(v___x_4304_);
lean_dec(v_index_4300_);
v___y_4271_ = v___x_4295_;
v___y_4272_ = v_decision_4287_;
v___y_4273_ = v_newArms_4288_;
v___y_4274_ = v___x_4292_;
goto v___jp_4270_;
}
else
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4307_ = lean_unsigned_to_nat(4u);
v___x_4308_ = lean_nat_mul(v___x_4304_, v___x_4307_);
v___x_4309_ = lean_unsigned_to_nat(3u);
v___x_4310_ = lean_nat_mul(v___x_4305_, v___x_4309_);
v___x_4311_ = lean_nat_dec_le(v___x_4308_, v___x_4310_);
lean_dec(v___x_4310_);
lean_dec(v___x_4308_);
if (v___x_4311_ == 0)
{
lean_dec(v___x_4304_);
lean_dec(v_index_4300_);
v___y_4271_ = v___x_4295_;
v___y_4272_ = v_decision_4287_;
v___y_4273_ = v_newArms_4288_;
v___y_4274_ = v___x_4292_;
goto v___jp_4270_;
}
else
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Std_DHashMap_Raw_setEntry___redArg(v_newArms_4288_, v___x_4304_, v_index_4300_, v___x_4236_, v___x_4295_);
lean_dec(v_index_4300_);
v___y_4226_ = v_decision_4287_;
v___y_4227_ = v___x_4292_;
v___y_4228_ = v___x_4312_;
goto v___jp_4225_;
}
}
}
default: 
{
lean_object* v_size_4313_; lean_object* v_keyArray_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v_size_4313_ = lean_ctor_get(v_newArms_4288_, 0);
v_keyArray_4314_ = lean_ctor_get(v_newArms_4288_, 1);
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = lean_nat_add(v_size_4313_, v___x_4315_);
v___x_4317_ = lean_array_get_size(v_keyArray_4314_);
v___x_4318_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; 
lean_dec(v___x_4316_);
v___x_4319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_newArms_4288_);
lean_dec_ref(v_newArms_4288_);
v___y_4248_ = v___x_4295_;
v___y_4249_ = v_decision_4287_;
v___y_4250_ = v___x_4292_;
v___y_4251_ = v___x_4319_;
goto v___jp_4247_;
}
else
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
v___x_4320_ = lean_unsigned_to_nat(4u);
v___x_4321_ = lean_nat_mul(v___x_4316_, v___x_4320_);
lean_dec(v___x_4316_);
v___x_4322_ = lean_unsigned_to_nat(3u);
v___x_4323_ = lean_nat_mul(v___x_4317_, v___x_4322_);
v___x_4324_ = lean_nat_dec_le(v___x_4321_, v___x_4323_);
lean_dec(v___x_4323_);
lean_dec(v___x_4321_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4325_; 
v___x_4325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(v_newArms_4288_);
lean_dec_ref(v_newArms_4288_);
v___y_4248_ = v___x_4295_;
v___y_4249_ = v_decision_4287_;
v___y_4250_ = v___x_4292_;
v___y_4251_ = v___x_4325_;
goto v___jp_4247_;
}
else
{
v___y_4248_ = v___x_4295_;
v___y_4249_ = v_decision_4287_;
v___y_4250_ = v___x_4292_;
v___y_4251_ = v_newArms_4288_;
goto v___jp_4247_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_4236_);
lean_dec_ref(v_decl_4217_);
return v___y_4285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec(v_a_4352_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_4360_, lean_object* v_b_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
if (lean_obj_tag(v_as_x27_4360_) == 0)
{
lean_object* v___x_4369_; 
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v_b_4361_);
return v___x_4369_;
}
else
{
lean_object* v_head_4370_; lean_object* v_tail_4371_; lean_object* v___x_4372_; lean_object* v_decision_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v_head_4370_ = lean_ctor_get(v_as_x27_4360_, 0);
v_tail_4371_ = lean_ctor_get(v_as_x27_4360_, 1);
v___x_4372_ = lean_st_ref_get(v___y_4362_);
v_decision_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc_ref(v_decision_4373_);
lean_dec(v___x_4372_);
v___x_4374_ = lean_box(0);
v___x_4375_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_4370_);
v___x_4376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_4373_, v___x_4375_);
lean_dec(v___x_4375_);
lean_dec_ref(v_decision_4373_);
v___x_4377_ = lean_box(3);
v___x_4378_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_4376_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4379_ = lean_box(2);
v___x_4380_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_4376_, v___x_4379_);
lean_dec(v___x_4376_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; 
lean_inc(v_head_4370_);
v___x_4381_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_4370_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_dec_ref_known(v___x_4381_, 1);
v_as_x27_4360_ = v_tail_4371_;
v_b_4361_ = v___x_4374_;
goto _start;
}
else
{
return v___x_4381_;
}
}
else
{
lean_object* v___x_4383_; 
lean_inc(v_head_4370_);
v___x_4383_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_4370_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_dec_ref_known(v___x_4383_, 1);
v_as_x27_4360_ = v_tail_4371_;
v_b_4361_ = v___x_4374_;
goto _start;
}
else
{
return v___x_4383_;
}
}
}
else
{
uint8_t v___x_4385_; lean_object* v___x_4386_; 
lean_dec(v___x_4376_);
v___x_4385_ = 0;
v___x_4386_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_4385_, v_head_4370_, v___y_4365_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_dec_ref_known(v___x_4386_, 1);
v_as_x27_4360_ = v_tail_4371_;
v_b_4361_ = v___x_4374_;
goto _start;
}
else
{
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_4388_, lean_object* v_b_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_4388_, v_b_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec(v_as_x27_4388_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = lean_box(0);
v___x_4406_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_4399_, v___x_4405_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v___x_4406_, 0);
lean_dec(v_unused_4414_);
v___x_4408_ = v___x_4406_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_dec(v___x_4406_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4405_);
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4405_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
else
{
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
lean_dec(v_a_4418_);
lean_dec_ref(v_a_4417_);
lean_dec(v_a_4416_);
lean_dec(v_a_4415_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_4423_, lean_object* v_as_x27_4424_, lean_object* v_b_4425_, lean_object* v_a_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_4424_, v_b_4425_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_4435_, lean_object* v_as_x27_4436_, lean_object* v_b_4437_, lean_object* v_a_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_4435_, v_as_x27_4436_, v_b_4437_, v_a_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec(v_as_x27_4436_);
lean_dec(v_as_4435_);
return v_res_4446_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4447_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_4451_ = lean_unsigned_to_nat(0u);
v___x_4452_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
lean_ctor_set(v___x_4452_, 2, v___x_4451_);
lean_ctor_set(v___x_4452_, 3, v___x_4451_);
lean_ctor_set(v___x_4452_, 4, v___x_4450_);
lean_ctor_set(v___x_4452_, 5, v___x_4450_);
lean_ctor_set(v___x_4452_, 6, v___x_4450_);
lean_ctor_set(v___x_4452_, 7, v___x_4450_);
lean_ctor_set(v___x_4452_, 8, v___x_4450_);
lean_ctor_set(v___x_4452_, 9, v___x_4450_);
lean_ctor_set(v___x_4452_, 10, v___x_4450_);
return v___x_4452_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4453_; double v___x_4454_; 
v___x_4453_ = lean_unsigned_to_nat(0u);
v___x_4454_ = lean_float_of_nat(v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_4458_, lean_object* v_msg_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_options_4465_; lean_object* v_ref_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_options_4465_ = lean_ctor_get(v___y_4462_, 2);
v_ref_4466_ = lean_ctor_get(v___y_4462_, 5);
v___x_4467_ = lean_st_ref_get(v___y_4463_);
v___x_4468_ = lean_st_ref_get(v___y_4461_);
v___x_4469_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4460_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4528_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4472_ = v___x_4469_;
v_isShared_4473_ = v_isSharedCheck_4528_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4528_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_env_4474_; lean_object* v_lctx_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4526_; 
v_env_4474_ = lean_ctor_get(v___x_4467_, 0);
lean_inc_ref(v_env_4474_);
lean_dec(v___x_4467_);
v_lctx_4475_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; 
v_unused_4527_ = lean_ctor_get(v___x_4468_, 1);
lean_dec(v_unused_4527_);
v___x_4477_ = v___x_4468_;
v_isShared_4478_ = v_isSharedCheck_4526_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_lctx_4475_);
lean_dec(v___x_4468_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4526_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v_traceState_4481_; lean_object* v_env_4482_; lean_object* v_nextMacroScope_4483_; lean_object* v_ngen_4484_; lean_object* v_auxDeclNGen_4485_; lean_object* v_cache_4486_; lean_object* v_messages_4487_; lean_object* v_infoState_4488_; lean_object* v_snapshotTasks_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4525_; 
v___x_4479_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_4480_ = lean_st_ref_take(v___y_4463_);
v_traceState_4481_ = lean_ctor_get(v___x_4480_, 4);
v_env_4482_ = lean_ctor_get(v___x_4480_, 0);
v_nextMacroScope_4483_ = lean_ctor_get(v___x_4480_, 1);
v_ngen_4484_ = lean_ctor_get(v___x_4480_, 2);
v_auxDeclNGen_4485_ = lean_ctor_get(v___x_4480_, 3);
v_cache_4486_ = lean_ctor_get(v___x_4480_, 5);
v_messages_4487_ = lean_ctor_get(v___x_4480_, 6);
v_infoState_4488_ = lean_ctor_get(v___x_4480_, 7);
v_snapshotTasks_4489_ = lean_ctor_get(v___x_4480_, 8);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4491_ = v___x_4480_;
v_isShared_4492_ = v_isSharedCheck_4525_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_snapshotTasks_4489_);
lean_inc(v_infoState_4488_);
lean_inc(v_messages_4487_);
lean_inc(v_cache_4486_);
lean_inc(v_traceState_4481_);
lean_inc(v_auxDeclNGen_4485_);
lean_inc(v_ngen_4484_);
lean_inc(v_nextMacroScope_4483_);
lean_inc(v_env_4482_);
lean_dec(v___x_4480_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4525_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
uint64_t v_tid_4493_; lean_object* v_traces_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4524_; 
v_tid_4493_ = lean_ctor_get_uint64(v_traceState_4481_, sizeof(void*)*1);
v_traces_4494_ = lean_ctor_get(v_traceState_4481_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_traceState_4481_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4496_ = v_traceState_4481_;
v_isShared_4497_ = v_isSharedCheck_4524_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_traces_4494_);
lean_dec(v_traceState_4481_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4524_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
uint8_t v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4498_ = lean_unbox(v_a_4470_);
lean_dec(v_a_4470_);
v___x_4499_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4475_, v___x_4498_);
lean_dec_ref(v_lctx_4475_);
lean_inc_ref(v_options_4465_);
v___x_4500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4500_, 0, v_env_4474_);
lean_ctor_set(v___x_4500_, 1, v___x_4479_);
lean_ctor_set(v___x_4500_, 2, v___x_4499_);
lean_ctor_set(v___x_4500_, 3, v_options_4465_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set_tag(v___x_4477_, 3);
lean_ctor_set(v___x_4477_, 1, v_msg_4459_);
lean_ctor_set(v___x_4477_, 0, v___x_4500_);
v___x_4502_ = v___x_4477_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_msg_4459_);
v___x_4502_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; double v___x_4504_; uint8_t v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4513_; 
v___x_4503_ = lean_box(0);
v___x_4504_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_4505_ = 0;
v___x_4506_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_4507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4507_, 0, v_cls_4458_);
lean_ctor_set(v___x_4507_, 1, v___x_4503_);
lean_ctor_set(v___x_4507_, 2, v___x_4506_);
lean_ctor_set_float(v___x_4507_, sizeof(void*)*3, v___x_4504_);
lean_ctor_set_float(v___x_4507_, sizeof(void*)*3 + 8, v___x_4504_);
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*3 + 16, v___x_4505_);
v___x_4508_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_4509_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4507_);
lean_ctor_set(v___x_4509_, 1, v___x_4502_);
lean_ctor_set(v___x_4509_, 2, v___x_4508_);
lean_inc(v_ref_4466_);
v___x_4510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4510_, 0, v_ref_4466_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = l_Lean_PersistentArray_push___redArg(v_traces_4494_, v___x_4510_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4511_);
v___x_4513_ = v___x_4496_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4511_);
lean_ctor_set_uint64(v_reuseFailAlloc_4522_, sizeof(void*)*1, v_tid_4493_);
v___x_4513_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
lean_object* v___x_4515_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 4, v___x_4513_);
v___x_4515_ = v___x_4491_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_env_4482_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_nextMacroScope_4483_);
lean_ctor_set(v_reuseFailAlloc_4521_, 2, v_ngen_4484_);
lean_ctor_set(v_reuseFailAlloc_4521_, 3, v_auxDeclNGen_4485_);
lean_ctor_set(v_reuseFailAlloc_4521_, 4, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4521_, 5, v_cache_4486_);
lean_ctor_set(v_reuseFailAlloc_4521_, 6, v_messages_4487_);
lean_ctor_set(v_reuseFailAlloc_4521_, 7, v_infoState_4488_);
lean_ctor_set(v_reuseFailAlloc_4521_, 8, v_snapshotTasks_4489_);
v___x_4515_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4519_; 
v___x_4516_ = lean_st_ref_put(v___y_4463_, v___x_4515_);
v___x_4517_ = lean_box(0);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4517_);
v___x_4519_ = v___x_4472_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4517_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v___x_4468_);
lean_dec(v___x_4467_);
lean_dec_ref(v_msg_4459_);
lean_dec(v_cls_4458_);
v_a_4529_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4469_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4469_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_4537_, lean_object* v_msg_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_4537_, v_msg_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_4545_, lean_object* v_msg_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_4545_, v_msg_4546_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_4554_, lean_object* v_msg_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_4554_, v_msg_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
return v_res_4562_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4572_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_4573_ = l_Lean_Name_append(v___x_4572_, v___x_4571_);
return v___x_4573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4575_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_4576_ = l_Lean_stringToMessageData(v___x_4575_);
return v___x_4576_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4578_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_4579_ = l_Lean_stringToMessageData(v___x_4578_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
switch(lean_obj_tag(v_code_4580_))
{
case 0:
{
lean_object* v_decl_4587_; lean_object* v_k_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v_decl_4587_ = lean_ctor_get(v_code_4580_, 0);
lean_inc_ref(v_decl_4587_);
v_k_4588_ = lean_ctor_get(v_code_4580_, 1);
lean_inc_ref(v_k_4588_);
lean_dec_ref_known(v_code_4580_, 2);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v_decl_4587_);
v___x_4590_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_4590_, 0, v_k_4588_);
v___x_4591_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_4589_, v___x_4590_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4591_;
}
case 1:
{
lean_object* v_decl_4592_; lean_object* v_k_4593_; lean_object* v_params_4594_; lean_object* v_type_4595_; lean_object* v_value_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v_decl_4592_ = lean_ctor_get(v_code_4580_, 0);
lean_inc_ref(v_decl_4592_);
v_k_4593_ = lean_ctor_get(v_code_4580_, 1);
lean_inc_ref(v_k_4593_);
lean_dec_ref_known(v_code_4580_, 2);
v_params_4594_ = lean_ctor_get(v_decl_4592_, 2);
lean_inc_ref(v_params_4594_);
v_type_4595_ = lean_ctor_get(v_decl_4592_, 3);
lean_inc_ref(v_type_4595_);
v_value_4596_ = lean_ctor_get(v_decl_4592_, 4);
lean_inc_ref(v_value_4596_);
v___x_4597_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_4597_, 0, v_value_4596_);
v___x_4598_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_4597_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4619_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4619_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4619_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
uint8_t v___x_4603_; lean_object* v___x_4604_; 
v___x_4603_ = 0;
v___x_4604_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4603_, v_decl_4592_, v_type_4595_, v_params_4594_, v_a_4599_, v_a_4583_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref_known(v___x_4604_, 1);
if (v_isShared_4602_ == 0)
{
lean_ctor_set_tag(v___x_4601_, 1);
lean_ctor_set(v___x_4601_, 0, v_a_4605_);
v___x_4607_ = v___x_4601_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4605_);
v___x_4607_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_4608_, 0, v_k_4593_);
v___x_4609_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_4607_, v___x_4608_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4609_;
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_del_object(v___x_4601_);
lean_dec_ref(v_k_4593_);
v_a_4611_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4604_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4604_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_4595_);
lean_dec_ref(v_params_4594_);
lean_dec_ref(v_k_4593_);
lean_dec_ref(v_decl_4592_);
return v___x_4598_;
}
}
case 2:
{
lean_object* v_decl_4620_; lean_object* v_k_4621_; lean_object* v_params_4622_; lean_object* v_type_4623_; lean_object* v_value_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v_decl_4620_ = lean_ctor_get(v_code_4580_, 0);
lean_inc_ref(v_decl_4620_);
v_k_4621_ = lean_ctor_get(v_code_4580_, 1);
lean_inc_ref(v_k_4621_);
lean_dec_ref_known(v_code_4580_, 2);
v_params_4622_ = lean_ctor_get(v_decl_4620_, 2);
lean_inc_ref(v_params_4622_);
v_type_4623_ = lean_ctor_get(v_decl_4620_, 3);
lean_inc_ref(v_type_4623_);
v_value_4624_ = lean_ctor_get(v_decl_4620_, 4);
lean_inc_ref(v_value_4624_);
v___x_4625_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_4625_, 0, v_value_4624_);
v___x_4626_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_4625_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4647_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4647_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4647_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
uint8_t v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = 0;
v___x_4632_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4631_, v_decl_4620_, v_type_4623_, v_params_4622_, v_a_4627_, v_a_4583_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___x_4635_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
if (v_isShared_4630_ == 0)
{
lean_ctor_set_tag(v___x_4629_, 2);
lean_ctor_set(v___x_4629_, 0, v_a_4633_);
v___x_4635_ = v___x_4629_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4633_);
v___x_4635_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_4636_, 0, v_k_4621_);
v___x_4637_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_4635_, v___x_4636_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4637_;
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_del_object(v___x_4629_);
lean_dec_ref(v_k_4621_);
v_a_4639_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4632_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4632_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_4623_);
lean_dec_ref(v_params_4622_);
lean_dec_ref(v_k_4621_);
lean_dec_ref(v_decl_4620_);
return v___x_4626_;
}
}
case 4:
{
lean_object* v_cases_4648_; lean_object* v___x_4649_; 
v_cases_4648_ = lean_ctor_get(v_code_4580_, 0);
lean_inc_ref_n(v_cases_4648_, 2);
v___x_4649_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_4648_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4650_);
lean_dec_ref_known(v___x_4649_, 1);
v___x_4651_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_4648_);
v___x_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4652_, 0, v_a_4650_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
v___x_4653_ = lean_st_mk_ref(v___x_4652_);
v___x_4654_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_4653_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_object* v___x_4655_; lean_object* v_typeName_4656_; lean_object* v_resultType_4657_; lean_object* v_discr_4658_; lean_object* v_alts_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4702_; 
lean_dec_ref_known(v___x_4654_, 1);
v___x_4655_ = lean_st_ref_get(v___x_4653_);
lean_dec(v___x_4653_);
v_typeName_4656_ = lean_ctor_get(v_cases_4648_, 0);
v_resultType_4657_ = lean_ctor_get(v_cases_4648_, 1);
v_discr_4658_ = lean_ctor_get(v_cases_4648_, 2);
v_alts_4659_ = lean_ctor_get(v_cases_4648_, 3);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_cases_4648_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4661_ = v_cases_4648_;
v_isShared_4662_ = v_isSharedCheck_4702_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_alts_4659_);
lean_inc(v_discr_4658_);
lean_inc(v_resultType_4657_);
lean_inc(v_typeName_4656_);
lean_dec(v_cases_4648_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4702_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v_newArms_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v_newArms_4663_ = lean_ctor_get(v___x_4655_, 1);
lean_inc_ref(v_newArms_4663_);
lean_dec(v___x_4655_);
v___x_4664_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_4659_);
v___x_4665_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_4663_, v___x_4664_, v_alts_4659_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4693_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4693_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4693_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
uint8_t v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___y_4674_; uint8_t v___y_4686_; size_t v___x_4688_; size_t v___x_4689_; uint8_t v___x_4690_; 
v___x_4670_ = 0;
v___x_4671_ = lean_box(2);
v___x_4672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_4663_, v___x_4671_);
lean_dec_ref(v_newArms_4663_);
v___x_4688_ = lean_ptr_addr(v_alts_4659_);
lean_dec_ref(v_alts_4659_);
v___x_4689_ = lean_ptr_addr(v_a_4666_);
v___x_4690_ = lean_usize_dec_eq(v___x_4688_, v___x_4689_);
if (v___x_4690_ == 0)
{
v___y_4686_ = v___x_4690_;
goto v___jp_4685_;
}
else
{
size_t v___x_4691_; uint8_t v___x_4692_; 
v___x_4691_ = lean_ptr_addr(v_resultType_4657_);
v___x_4692_ = lean_usize_dec_eq(v___x_4691_, v___x_4691_);
v___y_4686_ = v___x_4692_;
goto v___jp_4685_;
}
v___jp_4673_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4675_ = lean_array_mk(v___x_4672_);
v___x_4676_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4670_, v___x_4675_, v___y_4674_);
lean_dec_ref(v___x_4675_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4676_);
v___x_4678_ = v___x_4668_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
v___jp_4680_:
{
lean_object* v___x_4682_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 3, v_a_4666_);
v___x_4682_ = v___x_4661_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_typeName_4656_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v_resultType_4657_);
lean_ctor_set(v_reuseFailAlloc_4684_, 2, v_discr_4658_);
lean_ctor_set(v_reuseFailAlloc_4684_, 3, v_a_4666_);
v___x_4682_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
v___y_4674_ = v___x_4683_;
goto v___jp_4673_;
}
}
v___jp_4685_:
{
if (v___y_4686_ == 0)
{
lean_dec_ref_known(v_code_4580_, 1);
goto v___jp_4680_;
}
else
{
uint8_t v___x_4687_; 
v___x_4687_ = l_Lean_instBEqFVarId_beq(v_discr_4658_, v_discr_4658_);
if (v___x_4687_ == 0)
{
lean_dec_ref_known(v_code_4580_, 1);
goto v___jp_4680_;
}
else
{
lean_dec(v_a_4666_);
lean_del_object(v___x_4661_);
lean_dec(v_discr_4658_);
lean_dec_ref(v_resultType_4657_);
lean_dec(v_typeName_4656_);
v___y_4674_ = v_code_4580_;
goto v___jp_4673_;
}
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v_newArms_4663_);
lean_del_object(v___x_4661_);
lean_dec_ref(v_alts_4659_);
lean_dec(v_discr_4658_);
lean_dec_ref(v_resultType_4657_);
lean_dec(v_typeName_4656_);
lean_dec_ref_known(v_code_4580_, 1);
v_a_4694_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4665_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4665_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v___x_4653_);
lean_dec_ref_known(v_code_4580_, 1);
lean_dec_ref(v_cases_4648_);
v_a_4703_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4654_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4654_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec_ref_known(v_code_4580_, 1);
lean_dec_ref(v_cases_4648_);
v_a_4711_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4649_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4649_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
default: 
{
uint8_t v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4719_ = 0;
lean_inc(v_a_4581_);
v___x_4720_ = lean_array_mk(v_a_4581_);
v___x_4721_ = l_Array_reverse___redArg(v___x_4720_);
v___x_4722_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4719_, v___x_4721_, v_code_4580_);
lean_dec_ref(v___x_4721_);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4722_);
return v___x_4723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_4732_, lean_object* v_i_4733_, lean_object* v_as_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4741_ = lean_array_get_size(v_as_4734_);
v___x_4742_ = lean_nat_dec_lt(v_i_4733_, v___x_4741_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; 
lean_dec(v_i_4733_);
v___x_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4743_, 0, v_as_4734_);
return v___x_4743_;
}
else
{
lean_object* v_options_4744_; lean_object* v_inheritedTraceOptions_4745_; uint8_t v_hasTrace_4746_; uint8_t v___x_4747_; lean_object* v_a_4748_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; lean_object* v___y_4785_; 
v_options_4744_ = lean_ctor_get(v___y_4738_, 2);
v_inheritedTraceOptions_4745_ = lean_ctor_get(v___y_4738_, 13);
v_hasTrace_4746_ = lean_ctor_get_uint8(v_options_4744_, sizeof(void*)*1);
v___x_4747_ = 0;
v_a_4748_ = lean_array_fget_borrowed(v_as_4734_, v_i_4733_);
v___x_4779_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_4748_);
v___x_4780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_4732_, v___x_4779_);
if (v_hasTrace_4746_ == 0)
{
lean_dec(v___x_4779_);
v___y_4782_ = v___y_4736_;
v___y_4783_ = v___y_4737_;
v___y_4784_ = v___y_4738_;
v___y_4785_ = v___y_4739_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4790_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4791_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_4792_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4745_, v_options_4744_, v___x_4791_);
if (v___x_4792_ == 0)
{
lean_dec(v___x_4779_);
v___y_4782_ = v___y_4736_;
v___y_4783_ = v___y_4737_;
v___y_4784_ = v___y_4738_;
v___y_4785_ = v___y_4739_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4793_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_4794_ = lean_unsigned_to_nat(0u);
v___x_4795_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_4779_, v___x_4794_);
v___x_4796_ = l_Lean_MessageData_ofFormat(v___x_4795_);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4793_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_4799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4797_);
lean_ctor_set(v___x_4799_, 1, v___x_4798_);
v___x_4800_ = l_List_lengthTR___redArg(v___x_4780_);
v___x_4801_ = l_Nat_reprFast(v___x_4800_);
v___x_4802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
v___x_4803_ = l_Lean_MessageData_ofFormat(v___x_4802_);
v___x_4804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4799_);
lean_ctor_set(v___x_4804_, 1, v___x_4803_);
v___x_4805_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_4790_, v___x_4804_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_dec_ref_known(v___x_4805_, 1);
v___y_4782_ = v___y_4736_;
v___y_4783_ = v___y_4737_;
v___y_4784_ = v___y_4738_;
v___y_4785_ = v___y_4739_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
lean_dec(v___x_4780_);
lean_dec_ref(v_as_4734_);
lean_dec(v_i_4733_);
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4805_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
v___jp_4749_:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4756_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_4747_, v___y_4754_, v___y_4755_);
lean_dec_ref(v___y_4754_);
v___x_4757_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_4757_, 0, v___x_4756_);
v___x_4758_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_4757_, v___y_4753_, v___y_4751_, v___y_4750_, v___y_4752_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4760_; size_t v___x_4761_; size_t v___x_4762_; uint8_t v___x_4763_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v___x_4758_, 1);
lean_inc(v_a_4748_);
v___x_4760_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_4748_, v_a_4759_);
v___x_4761_ = lean_ptr_addr(v_a_4748_);
v___x_4762_ = lean_ptr_addr(v___x_4760_);
v___x_4763_ = lean_usize_dec_eq(v___x_4761_, v___x_4762_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4764_ = lean_unsigned_to_nat(1u);
v___x_4765_ = lean_nat_add(v_i_4733_, v___x_4764_);
v___x_4766_ = lean_array_fset(v_as_4734_, v_i_4733_, v___x_4760_);
lean_dec(v_i_4733_);
v_i_4733_ = v___x_4765_;
v_as_4734_ = v___x_4766_;
goto _start;
}
else
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
lean_dec_ref(v___x_4760_);
v___x_4768_ = lean_unsigned_to_nat(1u);
v___x_4769_ = lean_nat_add(v_i_4733_, v___x_4768_);
lean_dec(v_i_4733_);
v_i_4733_ = v___x_4769_;
goto _start;
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v_as_4734_);
lean_dec(v_i_4733_);
v_a_4771_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4758_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4758_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
v___jp_4781_:
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_array_mk(v___x_4780_);
switch(lean_obj_tag(v_a_4748_))
{
case 0:
{
lean_object* v_code_4787_; 
v_code_4787_ = lean_ctor_get(v_a_4748_, 2);
lean_inc_ref(v_code_4787_);
v___y_4750_ = v___y_4784_;
v___y_4751_ = v___y_4783_;
v___y_4752_ = v___y_4785_;
v___y_4753_ = v___y_4782_;
v___y_4754_ = v___x_4786_;
v___y_4755_ = v_code_4787_;
goto v___jp_4749_;
}
case 1:
{
lean_object* v_code_4788_; 
v_code_4788_ = lean_ctor_get(v_a_4748_, 1);
lean_inc_ref(v_code_4788_);
v___y_4750_ = v___y_4784_;
v___y_4751_ = v___y_4783_;
v___y_4752_ = v___y_4785_;
v___y_4753_ = v___y_4782_;
v___y_4754_ = v___x_4786_;
v___y_4755_ = v_code_4788_;
goto v___jp_4749_;
}
default: 
{
lean_object* v_code_4789_; 
v_code_4789_ = lean_ctor_get(v_a_4748_, 0);
lean_inc_ref(v_code_4789_);
v___y_4750_ = v___y_4784_;
v___y_4751_ = v___y_4783_;
v___y_4752_ = v___y_4785_;
v___y_4753_ = v___y_4782_;
v___y_4754_ = v___x_4786_;
v___y_4755_ = v_code_4789_;
goto v___jp_4749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_4814_, lean_object* v_i_4815_, lean_object* v_as_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_4814_, v_i_4815_, v_as_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
lean_dec(v___y_4817_);
lean_dec_ref(v___x_4814_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_4824_, lean_object* v_v_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
if (lean_obj_tag(v_v_4825_) == 0)
{
lean_object* v_code_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4856_; 
v_code_4832_ = lean_ctor_get(v_v_4825_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_v_4825_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4834_ = v_v_4825_;
v_isShared_4835_ = v_isSharedCheck_4856_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_code_4832_);
lean_dec(v_v_4825_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4856_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; 
lean_inc(v___y_4830_);
lean_inc_ref(v___y_4829_);
lean_inc(v___y_4828_);
lean_inc_ref(v___y_4827_);
lean_inc(v___y_4826_);
v___x_4836_ = lean_apply_7(v_f_4824_, v_code_4832_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, lean_box(0));
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4847_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4839_ = v___x_4836_;
v_isShared_4840_ = v_isSharedCheck_4847_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4836_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4847_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 0, v_a_4837_);
v___x_4842_ = v___x_4834_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4844_; 
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 0, v___x_4842_);
v___x_4844_ = v___x_4839_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_del_object(v___x_4834_);
v_a_4848_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4836_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4836_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
else
{
lean_object* v___x_4857_; 
lean_dec_ref(v_f_4824_);
v___x_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4857_, 0, v_v_4825_);
return v___x_4857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_4858_, lean_object* v_v_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_4858_, v_v_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_4867_, lean_object* v_f_4868_, lean_object* v_v_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v___x_4876_; 
v___x_4876_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_4868_, v_v_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_4877_, lean_object* v_f_4878_, lean_object* v_v_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
uint8_t v_pu_boxed_4886_; lean_object* v_res_4887_; 
v_pu_boxed_4886_ = lean_unbox(v_pu_4877_);
v_res_4887_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_4886_, v_f_4878_, v_v_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec(v___y_4880_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v_toSignature_4895_; lean_object* v_value_4896_; uint8_t v_recursive_4897_; lean_object* v_inlineAttr_x3f_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4924_; 
v_toSignature_4895_ = lean_ctor_get(v_decl_4889_, 0);
v_value_4896_ = lean_ctor_get(v_decl_4889_, 1);
v_recursive_4897_ = lean_ctor_get_uint8(v_decl_4889_, sizeof(void*)*3);
v_inlineAttr_x3f_4898_ = lean_ctor_get(v_decl_4889_, 2);
v_isSharedCheck_4924_ = !lean_is_exclusive(v_decl_4889_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4900_ = v_decl_4889_;
v_isShared_4901_ = v_isSharedCheck_4924_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_inlineAttr_x3f_4898_);
lean_inc(v_value_4896_);
lean_inc(v_toSignature_4895_);
lean_dec(v_decl_4889_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4924_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4902_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_4903_ = lean_box(0);
v___x_4904_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_4902_, v_value_4896_, v___x_4903_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4915_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4907_ = v___x_4904_;
v_isShared_4908_ = v_isSharedCheck_4915_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4915_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v_a_4905_);
v___x_4910_ = v___x_4900_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_toSignature_4895_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v_a_4905_);
lean_ctor_set(v_reuseFailAlloc_4914_, 2, v_inlineAttr_x3f_4898_);
lean_ctor_set_uint8(v_reuseFailAlloc_4914_, sizeof(void*)*3, v_recursive_4897_);
v___x_4910_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4912_; 
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4910_);
v___x_4912_ = v___x_4907_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_del_object(v___x_4900_);
lean_dec(v_inlineAttr_x3f_4898_);
lean_dec_ref(v_toSignature_4895_);
v_a_4916_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4904_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4904_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_4948_, lean_object* v___f_4949_, lean_object* v_occurrence_4950_, lean_object* v_h_4951_){
_start:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_4953_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_4952_, v_phase_4948_, v___f_4949_, v_occurrence_4950_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_4954_, lean_object* v___f_4955_, lean_object* v_occurrence_4956_, lean_object* v_h_4957_){
_start:
{
uint8_t v_phase_boxed_4958_; lean_object* v_res_4959_; 
v_phase_boxed_4958_ = lean_unbox(v_phase_4954_);
v_res_4959_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_4958_, v___f_4955_, v_occurrence_4956_, v_h_4957_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_4961_, lean_object* v_occurrence_4962_){
_start:
{
lean_object* v___f_4963_; lean_object* v___x_4964_; lean_object* v___f_4965_; lean_object* v___x_4966_; uint8_t v___x_4967_; lean_object* v___x_4968_; 
v___f_4963_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_4964_ = lean_box(v_phase_4961_);
v___f_4965_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4965_, 0, v___x_4964_);
lean_closure_set(v___f_4965_, 1, v___f_4963_);
lean_closure_set(v___f_4965_, 2, v_occurrence_4962_);
v___x_4966_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_4967_ = 0;
v___x_4968_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_4966_, v_phase_4961_, v___x_4967_, v___f_4965_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_4969_, lean_object* v_occurrence_4970_){
_start:
{
uint8_t v_phase_boxed_4971_; lean_object* v_res_4972_; 
v_phase_boxed_4971_ = lean_unbox(v_phase_4969_);
v_res_4972_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_4971_, v_occurrence_4970_);
return v_res_4972_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5024_ = lean_unsigned_to_nat(3411573818u);
v___x_5025_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_5026_ = l_Lean_Name_num___override(v___x_5025_, v___x_5024_);
return v___x_5026_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_5029_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_5030_ = l_Lean_Name_str___override(v___x_5029_, v___x_5028_);
return v___x_5030_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5032_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_5033_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_5034_ = l_Lean_Name_str___override(v___x_5033_, v___x_5032_);
return v___x_5034_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5035_ = lean_unsigned_to_nat(2u);
v___x_5036_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_5037_ = l_Lean_Name_num___override(v___x_5036_, v___x_5035_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5039_; uint8_t v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5039_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_5040_ = 1;
v___x_5041_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_5042_ = l_Lean_registerTraceClass(v___x_5039_, v___x_5040_, v___x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_5044_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
}
#ifdef __cplusplus
}
#endif
