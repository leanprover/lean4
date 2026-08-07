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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object* v_a_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
else
{
lean_object* v_key_339_; lean_object* v_tail_340_; uint8_t v___x_341_; 
v_key_339_ = lean_ctor_get(v_x_337_, 0);
v_tail_340_ = lean_ctor_get(v_x_337_, 2);
v___x_341_ = l_Lean_instBEqFVarId_beq(v_key_339_, v_a_336_);
if (v___x_341_ == 0)
{
v_x_337_ = v_tail_340_;
goto _start;
}
else
{
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_343_, v_x_344_);
lean_dec(v_x_344_);
lean_dec(v_a_343_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_buckets_349_; lean_object* v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v_fold_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_buckets_349_ = lean_ctor_get(v_m_347_, 1);
v___x_350_ = lean_array_get_size(v_buckets_349_);
v___x_351_ = l_Lean_instHashableFVarId_hash(v_a_348_);
v___x_352_ = 32ULL;
v___x_353_ = lean_uint64_shift_right(v___x_351_, v___x_352_);
v_fold_354_ = lean_uint64_xor(v___x_351_, v___x_353_);
v___x_355_ = 16ULL;
v___x_356_ = lean_uint64_shift_right(v_fold_354_, v___x_355_);
v___x_357_ = lean_uint64_xor(v_fold_354_, v___x_356_);
v___x_358_ = lean_uint64_to_usize(v___x_357_);
v___x_359_ = lean_usize_of_nat(v___x_350_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_sub(v___x_359_, v___x_360_);
v___x_362_ = lean_usize_land(v___x_358_, v___x_361_);
v___x_363_ = lean_array_uget_borrowed(v_buckets_349_, v___x_362_);
v___x_364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_348_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object* v_m_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_m_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
return v_x_369_;
}
else
{
lean_object* v_key_371_; lean_object* v_value_372_; lean_object* v_tail_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_396_; 
v_key_371_ = lean_ctor_get(v_x_370_, 0);
v_value_372_ = lean_ctor_get(v_x_370_, 1);
v_tail_373_ = lean_ctor_get(v_x_370_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_396_ == 0)
{
v___x_375_ = v_x_370_;
v_isShared_376_ = v_isSharedCheck_396_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_tail_373_);
lean_inc(v_value_372_);
lean_inc(v_key_371_);
lean_dec(v_x_370_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_396_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v_fold_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_377_ = lean_array_get_size(v_x_369_);
v___x_378_ = l_Lean_instHashableFVarId_hash(v_key_371_);
v___x_379_ = 32ULL;
v___x_380_ = lean_uint64_shift_right(v___x_378_, v___x_379_);
v_fold_381_ = lean_uint64_xor(v___x_378_, v___x_380_);
v___x_382_ = 16ULL;
v___x_383_ = lean_uint64_shift_right(v_fold_381_, v___x_382_);
v___x_384_ = lean_uint64_xor(v_fold_381_, v___x_383_);
v___x_385_ = lean_uint64_to_usize(v___x_384_);
v___x_386_ = lean_usize_of_nat(v___x_377_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_sub(v___x_386_, v___x_387_);
v___x_389_ = lean_usize_land(v___x_385_, v___x_388_);
v___x_390_ = lean_array_uget_borrowed(v_x_369_, v___x_389_);
lean_inc(v___x_390_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 2, v___x_390_);
v___x_392_ = v___x_375_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_key_371_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_value_372_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v___x_390_);
v___x_392_ = v_reuseFailAlloc_395_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; 
v___x_393_ = lean_array_uset(v_x_369_, v___x_389_, v___x_392_);
v_x_369_ = v___x_393_;
v_x_370_ = v_tail_373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(lean_object* v_i_397_, lean_object* v_source_398_, lean_object* v_target_399_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_array_get_size(v_source_398_);
v___x_401_ = lean_nat_dec_lt(v_i_397_, v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_source_398_);
lean_dec(v_i_397_);
return v_target_399_;
}
else
{
lean_object* v_es_402_; lean_object* v___x_403_; lean_object* v_source_404_; lean_object* v_target_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_es_402_ = lean_array_fget(v_source_398_, v_i_397_);
v___x_403_ = lean_box(0);
v_source_404_ = lean_array_fset(v_source_398_, v_i_397_, v___x_403_);
v_target_405_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_target_399_, v_es_402_);
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_add(v_i_397_, v___x_406_);
lean_dec(v_i_397_);
v_i_397_ = v___x_407_;
v_source_398_ = v_source_404_;
v_target_399_ = v_target_405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object* v_data_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_nbuckets_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_410_ = lean_array_get_size(v_data_409_);
v___x_411_ = lean_unsigned_to_nat(2u);
v_nbuckets_412_ = lean_nat_mul(v___x_410_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_box(0);
v___x_415_ = lean_mk_array(v_nbuckets_412_, v___x_414_);
v___x_416_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v___x_413_, v_data_409_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object* v_m_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
lean_object* v_size_420_; lean_object* v_buckets_421_; lean_object* v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v_fold_426_; uint64_t v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; lean_object* v_bkt_435_; uint8_t v___x_436_; 
v_size_420_ = lean_ctor_get(v_m_417_, 0);
v_buckets_421_ = lean_ctor_get(v_m_417_, 1);
v___x_422_ = lean_array_get_size(v_buckets_421_);
v___x_423_ = l_Lean_instHashableFVarId_hash(v_a_418_);
v___x_424_ = 32ULL;
v___x_425_ = lean_uint64_shift_right(v___x_423_, v___x_424_);
v_fold_426_ = lean_uint64_xor(v___x_423_, v___x_425_);
v___x_427_ = 16ULL;
v___x_428_ = lean_uint64_shift_right(v_fold_426_, v___x_427_);
v___x_429_ = lean_uint64_xor(v_fold_426_, v___x_428_);
v___x_430_ = lean_uint64_to_usize(v___x_429_);
v___x_431_ = lean_usize_of_nat(v___x_422_);
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_sub(v___x_431_, v___x_432_);
v___x_434_ = lean_usize_land(v___x_430_, v___x_433_);
v_bkt_435_ = lean_array_uget_borrowed(v_buckets_421_, v___x_434_);
v___x_436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_418_, v_bkt_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
lean_inc_ref(v_buckets_421_);
lean_inc(v_size_420_);
v_isSharedCheck_457_ = !lean_is_exclusive(v_m_417_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_458_ = lean_ctor_get(v_m_417_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_m_417_, 0);
lean_dec(v_unused_459_);
v___x_438_ = v_m_417_;
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_m_417_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v_size_x27_441_; lean_object* v___x_442_; lean_object* v_buckets_x27_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v_size_x27_441_ = lean_nat_add(v_size_420_, v___x_440_);
lean_dec(v_size_420_);
lean_inc(v_bkt_435_);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v_a_418_);
lean_ctor_set(v___x_442_, 1, v_b_419_);
lean_ctor_set(v___x_442_, 2, v_bkt_435_);
v_buckets_x27_443_ = lean_array_uset(v_buckets_421_, v___x_434_, v___x_442_);
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_mul(v_size_x27_441_, v___x_444_);
v___x_446_ = lean_unsigned_to_nat(3u);
v___x_447_ = lean_nat_div(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_array_get_size(v_buckets_x27_443_);
v___x_449_ = lean_nat_dec_le(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
if (v___x_449_ == 0)
{
lean_object* v_val_450_; lean_object* v___x_452_; 
v_val_450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_443_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_val_450_);
lean_ctor_set(v___x_438_, 0, v_size_x27_441_);
v___x_452_ = v___x_438_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_size_x27_441_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_val_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_455_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_buckets_x27_443_);
lean_ctor_set(v___x_438_, 0, v_size_x27_441_);
v___x_455_ = v___x_438_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_size_x27_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_buckets_x27_443_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_dec(v_b_419_);
lean_dec(v_a_418_);
return v_m_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object* v_var_460_, uint8_t v_borrowed_461_, lean_object* v_a_462_){
_start:
{
if (lean_obj_tag(v_var_460_) == 1)
{
lean_object* v_fvarId_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_482_; 
v_fvarId_464_ = lean_ctor_get(v_var_460_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v_var_460_);
if (v_isSharedCheck_482_ == 0)
{
v___x_466_ = v_var_460_;
v_isShared_467_ = v_isSharedCheck_482_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_fvarId_464_);
lean_dec(v_var_460_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_482_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_st_ref_get(v_a_462_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_468_, v_fvarId_464_);
lean_dec(v___x_468_);
if (v_borrowed_461_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_470_ = lean_st_ref_take(v_a_462_);
v___x_471_ = lean_box(0);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_470_, v_fvarId_464_, v___x_471_);
v___x_473_ = lean_st_ref_set(v_a_462_, v___x_472_);
v___x_474_ = lean_box(v___x_469_);
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 0);
lean_ctor_set(v___x_466_, 0, v___x_474_);
v___x_476_ = v___x_466_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec(v_fvarId_464_);
v___x_478_ = lean_box(v___x_469_);
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 0);
lean_ctor_set(v___x_466_, 0, v___x_478_);
v___x_480_ = v___x_466_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_var_460_);
v___x_483_ = 0;
v___x_484_ = lean_box(v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object* v_var_486_, lean_object* v_borrowed_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
uint8_t v_borrowed_boxed_490_; lean_object* v_res_491_; 
v_borrowed_boxed_490_ = lean_unbox(v_borrowed_487_);
v_res_491_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_486_, v_borrowed_boxed_490_, v_a_488_);
lean_dec(v_a_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object* v_var_492_, uint8_t v_borrowed_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_492_, v_borrowed_493_, v_a_494_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object* v_var_501_, lean_object* v_borrowed_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
uint8_t v_borrowed_boxed_509_; lean_object* v_res_510_; 
v_borrowed_boxed_509_ = lean_unbox(v_borrowed_502_);
v_res_510_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_501_, v_borrowed_boxed_509_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
return v_res_510_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object* v_00_u03b2_511_, lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_512_, v_a_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object* v_00_u03b2_515_, lean_object* v_m_516_, lean_object* v_a_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_515_, v_m_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_m_516_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object* v_00_u03b2_520_, lean_object* v_m_521_, lean_object* v_a_522_, lean_object* v_b_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_521_, v_a_522_, v_b_523_);
return v___x_524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_529_, v_a_530_, v_x_531_);
lean_dec(v_x_531_);
lean_dec(v_a_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object* v_00_u03b2_534_, lean_object* v_data_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_data_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_537_, lean_object* v_i_538_, lean_object* v_source_539_, lean_object* v_target_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v_i_538_, v_source_539_, v_target_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object* v_as_546_, size_t v_i_547_, size_t v_stop_548_, uint8_t v_b_549_, lean_object* v___y_550_){
_start:
{
uint8_t v_a_553_; lean_object* v___y_558_; uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_eq(v_i_547_, v_stop_548_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_array_uget_borrowed(v_as_546_, v_i_547_);
lean_inc(v___x_562_);
v___x_563_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_562_, v___x_561_, v___y_550_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; uint8_t v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
v___x_565_ = lean_unbox(v_a_564_);
lean_dec(v_a_564_);
if (v___x_565_ == 0)
{
lean_dec_ref_known(v___x_563_, 1);
v_a_553_ = v_b_549_;
goto v___jp_552_;
}
else
{
v___y_558_ = v___x_563_;
goto v___jp_557_;
}
}
else
{
v___y_558_ = v___x_563_;
goto v___jp_557_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(v_b_549_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
v___jp_552_:
{
size_t v___x_554_; size_t v___x_555_; 
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_547_, v___x_554_);
v_i_547_ = v___x_555_;
v_b_549_ = v_a_553_;
goto _start;
}
v___jp_557_:
{
if (lean_obj_tag(v___y_558_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; 
v_a_559_ = lean_ctor_get(v___y_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___y_558_, 1);
v___x_560_ = lean_unbox(v_a_559_);
lean_dec(v_a_559_);
v_a_553_ = v___x_560_;
goto v___jp_552_;
}
else
{
return v___y_558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_568_, lean_object* v_i_569_, lean_object* v_stop_570_, lean_object* v_b_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v_i_boxed_574_; size_t v_stop_boxed_575_; uint8_t v_b_boxed_576_; lean_object* v_res_577_; 
v_i_boxed_574_ = lean_unbox_usize(v_i_569_);
lean_dec(v_i_569_);
v_stop_boxed_575_ = lean_unbox_usize(v_stop_570_);
lean_dec(v_stop_570_);
v_b_boxed_576_ = lean_unbox(v_b_571_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_568_, v_i_boxed_574_, v_stop_boxed_575_, v_b_boxed_576_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v_as_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_578_, lean_object* v_args_579_, lean_object* v_val_580_, lean_object* v_a_581_, uint8_t v_b_582_, lean_object* v___y_583_){
_start:
{
uint8_t v_a_586_; uint8_t v___x_590_; 
v___x_590_ = lean_nat_dec_lt(v_a_581_, v_upperBound_578_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_a_581_);
v___x_591_ = lean_box(v_b_582_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
else
{
lean_object* v_params_593_; lean_object* v___x_594_; uint8_t v___y_596_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_params_593_ = lean_ctor_get(v_val_580_, 3);
v___x_594_ = lean_array_fget_borrowed(v_args_579_, v_a_581_);
v___x_601_ = lean_array_get_size(v_params_593_);
v___x_602_ = lean_nat_dec_lt(v_a_581_, v___x_601_);
if (v___x_602_ == 0)
{
v___y_596_ = v___x_602_;
goto v___jp_595_;
}
else
{
lean_object* v___x_603_; uint8_t v_borrow_604_; 
v___x_603_ = lean_array_fget_borrowed(v_params_593_, v_a_581_);
v_borrow_604_ = lean_ctor_get_uint8(v___x_603_, sizeof(void*)*3);
v___y_596_ = v_borrow_604_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_597_; 
lean_inc(v___x_594_);
v___x_597_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_594_, v___y_596_, v___y_583_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; uint8_t v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = lean_unbox(v_a_598_);
if (v___x_599_ == 0)
{
lean_dec(v_a_598_);
v_a_586_ = v_b_582_;
goto v___jp_585_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
v_a_586_ = v___x_600_;
goto v___jp_585_;
}
}
else
{
lean_dec(v_a_581_);
return v___x_597_;
}
}
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_add(v_a_581_, v___x_587_);
lean_dec(v_a_581_);
v_a_581_ = v___x_588_;
v_b_582_ = v_a_586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object* v_upperBound_605_, lean_object* v_args_606_, lean_object* v_val_607_, lean_object* v_a_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v_b_boxed_612_; lean_object* v_res_613_; 
v_b_boxed_612_ = lean_unbox(v_b_609_);
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_605_, v_args_606_, v_val_607_, v_a_608_, v_b_boxed_612_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v_val_607_);
lean_dec_ref(v_args_606_);
lean_dec(v_upperBound_605_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_, uint8_t v_b_617_, lean_object* v___y_618_){
_start:
{
uint8_t v_a_621_; lean_object* v___y_626_; uint8_t v___x_629_; 
v___x_629_ = lean_usize_dec_eq(v_i_615_, v_stop_616_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_array_uget_borrowed(v_as_614_, v_i_615_);
lean_inc(v___x_630_);
v___x_631_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_630_, v___x_629_, v___y_618_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; uint8_t v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
v___x_633_ = lean_unbox(v_a_632_);
lean_dec(v_a_632_);
if (v___x_633_ == 0)
{
lean_dec_ref_known(v___x_631_, 1);
v_a_621_ = v_b_617_;
goto v___jp_620_;
}
else
{
v___y_626_ = v___x_631_;
goto v___jp_625_;
}
}
else
{
v___y_626_ = v___x_631_;
goto v___jp_625_;
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(v_b_617_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
v___jp_620_:
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_615_, v___x_622_);
v_i_615_ = v___x_623_;
v_b_617_ = v_a_621_;
goto _start;
}
v___jp_625_:
{
if (lean_obj_tag(v___y_626_) == 0)
{
lean_object* v_a_627_; uint8_t v___x_628_; 
v_a_627_ = lean_ctor_get(v___y_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___y_626_, 1);
v___x_628_ = lean_unbox(v_a_627_);
lean_dec(v_a_627_);
v_a_621_ = v___x_628_;
goto v___jp_620_;
}
else
{
return v___y_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_636_, lean_object* v_i_637_, lean_object* v_stop_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_i_boxed_642_; size_t v_stop_boxed_643_; uint8_t v_b_boxed_644_; lean_object* v_res_645_; 
v_i_boxed_642_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_stop_boxed_643_ = lean_unbox_usize(v_stop_638_);
lean_dec(v_stop_638_);
v_b_boxed_644_ = lean_unbox(v_b_639_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_636_, v_i_boxed_642_, v_stop_boxed_643_, v_b_boxed_644_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v_as_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object* v_value_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
switch(lean_obj_tag(v_value_646_))
{
case 0:
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v_isSharedCheck_661_ = !lean_is_exclusive(v_value_646_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_value_646_, 0);
lean_dec(v_unused_662_);
v___x_654_ = v_value_646_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_value_646_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = 0;
v___x_657_ = lean_box(v___x_656_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
case 1:
{
uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = 0;
v___x_664_ = lean_box(v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
case 2:
{
lean_object* v_struct_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; 
v_struct_666_ = lean_ctor_get(v_value_646_, 2);
lean_inc(v_struct_666_);
lean_dec_ref_known(v_value_646_, 3);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_struct_666_);
v___x_668_ = 1;
v___x_669_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_667_, v___x_668_, v_a_647_);
return v___x_669_;
}
case 3:
{
lean_object* v_declName_670_; lean_object* v_args_671_; lean_object* v___x_672_; 
v_declName_670_ = lean_ctor_get(v_value_646_, 0);
lean_inc(v_declName_670_);
v_args_671_ = lean_ctor_get(v_value_646_, 2);
lean_inc_ref(v_args_671_);
lean_dec_ref_known(v_value_646_, 3);
v___x_672_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_670_, v_a_651_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_701_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_701_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_701_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_701_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 0)
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_677_ = 0;
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_array_get_size(v_args_671_);
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_683_; 
lean_dec_ref(v_args_671_);
v___x_681_ = lean_box(v___x_677_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_681_);
v___x_683_ = v___x_675_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_le(v___x_679_, v___x_679_);
if (v___x_685_ == 0)
{
if (v___x_680_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_688_; 
lean_dec_ref(v_args_671_);
v___x_686_ = lean_box(v___x_677_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_686_);
v___x_688_ = v___x_675_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
lean_del_object(v___x_675_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_679_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_671_, v___x_690_, v___x_691_, v___x_677_, v_a_647_);
lean_dec_ref(v_args_671_);
return v___x_692_;
}
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
lean_del_object(v___x_675_);
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_679_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_671_, v___x_693_, v___x_694_, v___x_677_, v_a_647_);
lean_dec_ref(v_args_671_);
return v___x_695_;
}
}
}
else
{
lean_object* v_val_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; 
lean_del_object(v___x_675_);
v_val_696_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_a_673_, 1);
v___x_697_ = lean_array_get_size(v_args_671_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = 0;
v___x_700_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_697_, v_args_671_, v_val_696_, v___x_698_, v___x_699_, v_a_647_);
lean_dec(v_val_696_);
lean_dec_ref(v_args_671_);
return v___x_700_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_args_671_);
v_a_702_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_672_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_672_);
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
default: 
{
lean_object* v_fvarId_710_; lean_object* v_args_711_; lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_fvarId_710_ = lean_ctor_get(v_value_646_, 0);
lean_inc(v_fvarId_710_);
v_args_711_ = lean_ctor_get(v_value_646_, 1);
lean_inc_ref(v_args_711_);
lean_dec_ref_known(v_value_646_, 2);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_fvarId_710_);
v___x_713_ = 0;
v___x_714_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_712_, v___x_713_, v_a_647_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_array_get_size(v_args_711_);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v_a_715_);
lean_dec_ref(v_args_711_);
return v___x_714_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_le(v___x_717_, v___x_717_);
if (v___x_719_ == 0)
{
if (v___x_718_ == 0)
{
lean_dec(v_a_715_);
lean_dec_ref(v_args_711_);
return v___x_714_;
}
else
{
size_t v___x_720_; size_t v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
lean_dec_ref(v___x_714_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = lean_usize_of_nat(v___x_717_);
v___x_722_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_711_, v___x_720_, v___x_721_, v___x_722_, v_a_647_);
lean_dec_ref(v_args_711_);
return v___x_723_;
}
}
else
{
size_t v___x_724_; size_t v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v___x_714_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = lean_usize_of_nat(v___x_717_);
v___x_726_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_711_, v___x_724_, v___x_725_, v___x_726_, v_a_647_);
lean_dec_ref(v_args_711_);
return v___x_727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(lean_object* v_value_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object* v_env_736_, lean_object* v_value_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object* v_env_745_, lean_object* v_value_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_745_, v_value_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_env_745_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, uint8_t v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_754_, v_i_755_, v_stop_756_, v_b_757_, v___y_758_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object* v_as_765_, lean_object* v_i_766_, lean_object* v_stop_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
size_t v_i_boxed_775_; size_t v_stop_boxed_776_; uint8_t v_b_boxed_777_; lean_object* v_res_778_; 
v_i_boxed_775_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_stop_boxed_776_ = lean_unbox_usize(v_stop_767_);
lean_dec(v_stop_767_);
v_b_boxed_777_ = lean_unbox(v_b_768_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_765_, v_i_boxed_775_, v_stop_boxed_776_, v_b_boxed_777_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v_as_765_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object* v_upperBound_779_, lean_object* v_args_780_, lean_object* v_val_781_, lean_object* v_inst_782_, lean_object* v_R_783_, lean_object* v_a_784_, uint8_t v_b_785_, lean_object* v_c_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_779_, v_args_780_, v_val_781_, v_a_784_, v_b_785_, v___y_787_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object* v_upperBound_794_, lean_object* v_args_795_, lean_object* v_val_796_, lean_object* v_inst_797_, lean_object* v_R_798_, lean_object* v_a_799_, lean_object* v_b_800_, lean_object* v_c_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v_b_boxed_808_; lean_object* v_res_809_; 
v_b_boxed_808_ = lean_unbox(v_b_800_);
v_res_809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_794_, v_args_795_, v_val_796_, v_inst_797_, v_R_798_, v_a_799_, v_b_boxed_808_, v_c_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v_val_796_);
lean_dec_ref(v_args_795_);
lean_dec(v_upperBound_794_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object* v_as_810_, size_t v_i_811_, size_t v_stop_812_, uint8_t v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_810_, v_i_811_, v_stop_812_, v_b_813_, v___y_814_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object* v_as_821_, lean_object* v_i_822_, lean_object* v_stop_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
size_t v_i_boxed_831_; size_t v_stop_boxed_832_; uint8_t v_b_boxed_833_; lean_object* v_res_834_; 
v_i_boxed_831_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_stop_boxed_832_ = lean_unbox_usize(v_stop_823_);
lean_dec(v_stop_823_);
v_b_boxed_833_ = lean_unbox(v_b_824_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_821_, v_i_boxed_831_, v_stop_boxed_832_, v_b_boxed_833_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v_as_821_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object* v_value_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
if (lean_obj_tag(v_value_835_) == 0)
{
lean_object* v_decl_842_; lean_object* v_value_843_; lean_object* v___x_844_; 
v_decl_842_ = lean_ctor_get(v_value_835_, 0);
lean_inc_ref(v_decl_842_);
lean_dec_ref_known(v_value_835_, 1);
v_value_843_ = lean_ctor_get(v_decl_842_, 3);
lean_inc(v_value_843_);
lean_dec_ref(v_decl_842_);
v___x_844_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_843_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_844_;
}
else
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v_value_835_);
v___x_845_ = 0;
v___x_846_ = lean_box(v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object* v_value_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object* v_env_856_, lean_object* v_value_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object* v_env_865_, lean_object* v_value_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_865_, v_value_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_env_865_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_dec(v_b_875_);
lean_dec(v_a_874_);
return v_x_876_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_key_877_ = lean_ctor_get(v_x_876_, 0);
v_value_878_ = lean_ctor_get(v_x_876_, 1);
v_tail_879_ = lean_ctor_get(v_x_876_, 2);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v_x_876_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_inc(v_value_878_);
lean_inc(v_key_877_);
lean_dec(v_x_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; 
v___x_883_ = l_Lean_instBEqFVarId_beq(v_key_877_, v_a_874_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_874_, v_b_875_, v_tail_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 2, v___x_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_key_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_value_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v_value_878_);
lean_dec(v_key_877_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_b_875_);
lean_ctor_set(v___x_881_, 0, v_a_874_);
v___x_889_ = v___x_881_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_874_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_b_875_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_tail_879_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(lean_object* v_m_892_, lean_object* v_a_893_, lean_object* v_b_894_){
_start:
{
lean_object* v_size_895_; lean_object* v_buckets_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_939_; 
v_size_895_ = lean_ctor_get(v_m_892_, 0);
v_buckets_896_ = lean_ctor_get(v_m_892_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_m_892_);
if (v_isSharedCheck_939_ == 0)
{
v___x_898_ = v_m_892_;
v_isShared_899_ = v_isSharedCheck_939_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_buckets_896_);
lean_inc(v_size_895_);
lean_dec(v_m_892_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_939_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v_fold_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v_bkt_913_; uint8_t v___x_914_; 
v___x_900_ = lean_array_get_size(v_buckets_896_);
v___x_901_ = l_Lean_instHashableFVarId_hash(v_a_893_);
v___x_902_ = 32ULL;
v___x_903_ = lean_uint64_shift_right(v___x_901_, v___x_902_);
v_fold_904_ = lean_uint64_xor(v___x_901_, v___x_903_);
v___x_905_ = 16ULL;
v___x_906_ = lean_uint64_shift_right(v_fold_904_, v___x_905_);
v___x_907_ = lean_uint64_xor(v_fold_904_, v___x_906_);
v___x_908_ = lean_uint64_to_usize(v___x_907_);
v___x_909_ = lean_usize_of_nat(v___x_900_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_sub(v___x_909_, v___x_910_);
v___x_912_ = lean_usize_land(v___x_908_, v___x_911_);
v_bkt_913_ = lean_array_uget_borrowed(v_buckets_896_, v___x_912_);
v___x_914_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_893_, v_bkt_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v_size_x27_916_; lean_object* v___x_917_; lean_object* v_buckets_x27_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_915_ = lean_unsigned_to_nat(1u);
v_size_x27_916_ = lean_nat_add(v_size_895_, v___x_915_);
lean_dec(v_size_895_);
lean_inc(v_bkt_913_);
v___x_917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_917_, 0, v_a_893_);
lean_ctor_set(v___x_917_, 1, v_b_894_);
lean_ctor_set(v___x_917_, 2, v_bkt_913_);
v_buckets_x27_918_ = lean_array_uset(v_buckets_896_, v___x_912_, v___x_917_);
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_nat_mul(v_size_x27_916_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = lean_nat_div(v___x_920_, v___x_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_array_get_size(v_buckets_x27_918_);
v___x_924_ = lean_nat_dec_le(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
if (v___x_924_ == 0)
{
lean_object* v_val_925_; lean_object* v___x_927_; 
v_val_925_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_918_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_val_925_);
lean_ctor_set(v___x_898_, 0, v_size_x27_916_);
v___x_927_ = v___x_898_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_size_x27_916_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_val_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
lean_object* v___x_930_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_buckets_x27_918_);
lean_ctor_set(v___x_898_, 0, v_size_x27_916_);
v___x_930_ = v___x_898_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_size_x27_916_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_buckets_x27_918_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v___x_932_; lean_object* v_buckets_x27_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
lean_inc(v_bkt_913_);
v___x_932_ = lean_box(0);
v_buckets_x27_933_ = lean_array_uset(v_buckets_896_, v___x_912_, v___x_932_);
v___x_934_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_893_, v_b_894_, v_bkt_913_);
v___x_935_ = lean_array_uset(v_buckets_x27_933_, v___x_912_, v___x_934_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_935_);
v___x_937_ = v___x_898_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_size_895_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_935_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(lean_object* v_a_940_, lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_box(0);
return v___x_942_;
}
else
{
lean_object* v_key_943_; lean_object* v_value_944_; lean_object* v_tail_945_; uint8_t v___x_946_; 
v_key_943_ = lean_ctor_get(v_x_941_, 0);
v_value_944_ = lean_ctor_get(v_x_941_, 1);
v_tail_945_ = lean_ctor_get(v_x_941_, 2);
v___x_946_ = l_Lean_instBEqFVarId_beq(v_key_943_, v_a_940_);
if (v___x_946_ == 0)
{
v_x_941_ = v_tail_945_;
goto _start;
}
else
{
lean_object* v___x_948_; 
lean_inc(v_value_944_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_value_944_);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec(v_a_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_buckets_954_; lean_object* v___x_955_; uint64_t v___x_956_; uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v_fold_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_buckets_954_ = lean_ctor_get(v_m_952_, 1);
v___x_955_ = lean_array_get_size(v_buckets_954_);
v___x_956_ = l_Lean_instHashableFVarId_hash(v_a_953_);
v___x_957_ = 32ULL;
v___x_958_ = lean_uint64_shift_right(v___x_956_, v___x_957_);
v_fold_959_ = lean_uint64_xor(v___x_956_, v___x_958_);
v___x_960_ = 16ULL;
v___x_961_ = lean_uint64_shift_right(v_fold_959_, v___x_960_);
v___x_962_ = lean_uint64_xor(v_fold_959_, v___x_961_);
v___x_963_ = lean_uint64_to_usize(v___x_962_);
v___x_964_ = lean_usize_of_nat(v___x_955_);
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_sub(v___x_964_, v___x_965_);
v___x_967_ = lean_usize_land(v___x_963_, v___x_966_);
v___x_968_ = lean_array_uget_borrowed(v_buckets_954_, v___x_967_);
v___x_969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_953_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object* v_m_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_m_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* v_plannedDecision_973_, lean_object* v_var_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_st_ref_get(v_a_975_);
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_977_, v_var_974_);
lean_dec(v___x_977_);
if (lean_obj_tag(v___x_978_) == 1)
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1003_; 
v_val_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_1003_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1003_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
if (lean_obj_tag(v_val_979_) == 3)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_983_ = lean_st_ref_take(v_a_975_);
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_983_, v_var_974_, v_plannedDecision_973_);
v___x_985_ = lean_st_ref_set(v_a_975_, v___x_984_);
v___x_986_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 0, v___x_986_);
v___x_988_ = v___x_981_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
else
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_979_, v_plannedDecision_973_);
lean_dec(v_plannedDecision_973_);
lean_dec(v_val_979_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_991_ = lean_st_ref_take(v_a_975_);
v___x_992_ = lean_box(2);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_991_, v_var_974_, v___x_992_);
v___x_994_ = lean_st_ref_set(v_a_975_, v___x_993_);
v___x_995_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 0, v___x_995_);
v___x_997_ = v___x_981_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec(v_var_974_);
v___x_999_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 0, v___x_999_);
v___x_1001_ = v___x_981_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v___x_978_);
lean_dec(v_var_974_);
lean_dec(v_plannedDecision_973_);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_1006_, lean_object* v_var_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1006_, v_var_1007_, v_a_1008_);
lean_dec(v_a_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_1011_, lean_object* v_var_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1011_, v_var_1012_, v_a_1013_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_1021_, lean_object* v_var_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1021_, v_var_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec(v_a_1023_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_1031_, lean_object* v_m_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1032_, v_a_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1035_, lean_object* v_m_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1035_, v_m_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_m_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object* v_00_u03b2_1039_, lean_object* v_m_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_1040_, v_a_1041_, v_b_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object* v_00_u03b2_1044_, lean_object* v_a_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_1045_, v_x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1048_, lean_object* v_a_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_1048_, v_a_1049_, v_x_1050_);
lean_dec(v_x_1050_);
lean_dec(v_a_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object* v_00_u03b2_1052_, lean_object* v_a_1053_, lean_object* v_b_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_1053_, v_b_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1057_, lean_object* v_f_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
switch(lean_obj_tag(v_alt_1057_))
{
case 0:
{
lean_object* v_code_1066_; lean_object* v___x_1067_; 
v_code_1066_ = lean_ctor_get(v_alt_1057_, 2);
lean_inc_ref(v_code_1066_);
lean_dec_ref_known(v_alt_1057_, 3);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc(v___y_1059_);
v___x_1067_ = lean_apply_8(v_f_1058_, v_code_1066_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, lean_box(0));
return v___x_1067_;
}
case 1:
{
lean_object* v_code_1068_; lean_object* v___x_1069_; 
v_code_1068_ = lean_ctor_get(v_alt_1057_, 1);
lean_inc_ref(v_code_1068_);
lean_dec_ref_known(v_alt_1057_, 2);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc(v___y_1059_);
v___x_1069_ = lean_apply_8(v_f_1058_, v_code_1068_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, lean_box(0));
return v___x_1069_;
}
default: 
{
lean_object* v_code_1070_; lean_object* v___x_1071_; 
v_code_1070_ = lean_ctor_get(v_alt_1057_, 0);
lean_inc_ref(v_code_1070_);
lean_dec_ref_known(v_alt_1057_, 1);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc(v___y_1059_);
v___x_1071_ = lean_apply_8(v_f_1058_, v_code_1070_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, lean_box(0));
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1072_, lean_object* v_f_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1072_, v_f_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1081_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_instMonadEIO(lean_box(0));
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_toApplicative_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1160_; 
v___x_1095_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1096_ = l_StateRefT_x27_instMonad___redArg(v___x_1095_);
v_toApplicative_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1096_, 1);
lean_dec(v_unused_1161_);
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1160_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_toApplicative_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1160_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_toFunctor_1101_; lean_object* v_toSeq_1102_; lean_object* v_toSeqLeft_1103_; lean_object* v_toSeqRight_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1158_; 
v_toFunctor_1101_ = lean_ctor_get(v_toApplicative_1097_, 0);
v_toSeq_1102_ = lean_ctor_get(v_toApplicative_1097_, 2);
v_toSeqLeft_1103_ = lean_ctor_get(v_toApplicative_1097_, 3);
v_toSeqRight_1104_ = lean_ctor_get(v_toApplicative_1097_, 4);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_toApplicative_1097_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_toApplicative_1097_, 1);
lean_dec(v_unused_1159_);
v___x_1106_ = v_toApplicative_1097_;
v_isShared_1107_ = v_isSharedCheck_1158_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_toSeqRight_1104_);
lean_inc(v_toSeqLeft_1103_);
lean_inc(v_toSeq_1102_);
lean_inc(v_toFunctor_1101_);
lean_dec(v_toApplicative_1097_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1158_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___x_1117_; 
v___f_1108_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1109_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1101_);
v___f_1110_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1110_, 0, v_toFunctor_1101_);
v___f_1111_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1111_, 0, v_toFunctor_1101_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___f_1110_);
lean_ctor_set(v___x_1112_, 1, v___f_1111_);
v___f_1113_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1113_, 0, v_toSeqRight_1104_);
v___f_1114_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1114_, 0, v_toSeqLeft_1103_);
v___f_1115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1115_, 0, v_toSeq_1102_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v___f_1113_);
lean_ctor_set(v___x_1106_, 3, v___f_1114_);
lean_ctor_set(v___x_1106_, 2, v___f_1115_);
lean_ctor_set(v___x_1106_, 1, v___f_1108_);
lean_ctor_set(v___x_1106_, 0, v___x_1112_);
v___x_1117_ = v___x_1106_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___f_1108_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v___f_1115_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v___f_1114_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v___f_1113_);
v___x_1117_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v___f_1109_);
lean_ctor_set(v___x_1099_, 0, v___x_1117_);
v___x_1119_ = v___x_1099_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___f_1109_);
v___x_1119_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v_toApplicative_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1154_; 
v___x_1120_ = l_StateRefT_x27_instMonad___redArg(v___x_1119_);
v_toApplicative_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1120_, 1);
lean_dec(v_unused_1155_);
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1154_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_toApplicative_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1154_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_toFunctor_1125_; lean_object* v_toSeq_1126_; lean_object* v_toSeqLeft_1127_; lean_object* v_toSeqRight_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1152_; 
v_toFunctor_1125_ = lean_ctor_get(v_toApplicative_1121_, 0);
v_toSeq_1126_ = lean_ctor_get(v_toApplicative_1121_, 2);
v_toSeqLeft_1127_ = lean_ctor_get(v_toApplicative_1121_, 3);
v_toSeqRight_1128_ = lean_ctor_get(v_toApplicative_1121_, 4);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_toApplicative_1121_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_toApplicative_1121_, 1);
lean_dec(v_unused_1153_);
v___x_1130_ = v_toApplicative_1121_;
v_isShared_1131_ = v_isSharedCheck_1152_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_toSeqRight_1128_);
lean_inc(v_toSeqLeft_1127_);
lean_inc(v_toSeq_1126_);
lean_inc(v_toFunctor_1125_);
lean_dec(v_toApplicative_1121_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1152_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___x_1141_; 
v___f_1132_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1133_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1125_);
v___f_1134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1134_, 0, v_toFunctor_1125_);
v___f_1135_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1135_, 0, v_toFunctor_1125_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___f_1134_);
lean_ctor_set(v___x_1136_, 1, v___f_1135_);
v___f_1137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1137_, 0, v_toSeqRight_1128_);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1138_, 0, v_toSeqLeft_1127_);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1139_, 0, v_toSeq_1126_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v___f_1137_);
lean_ctor_set(v___x_1130_, 3, v___f_1138_);
lean_ctor_set(v___x_1130_, 2, v___f_1139_);
lean_ctor_set(v___x_1130_, 1, v___f_1132_);
lean_ctor_set(v___x_1130_, 0, v___x_1136_);
v___x_1141_ = v___x_1130_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___f_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v___f_1139_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v___f_1138_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v___f_1137_);
v___x_1141_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___f_1133_);
lean_ctor_set(v___x_1123_, 0, v___x_1141_);
v___x_1143_ = v___x_1123_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___f_1133_);
v___x_1143_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_9302__overap_1148_; lean_object* v___x_1149_; 
v___x_1144_ = l_ReaderT_instMonad___redArg(v___x_1143_);
v___x_1145_ = l_StateRefT_x27_instMonad___redArg(v___x_1144_);
v___x_1146_ = lean_box(0);
v___x_1147_ = l_instInhabitedOfMonad___redArg(v___x_1145_, v___x_1146_);
v___x_9302__overap_1148_ = lean_panic_fn_borrowed(v___x_1147_, v_msg_1087_);
lean_dec(v___x_1147_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1089_);
lean_inc(v___y_1088_);
v___x_1149_ = lean_apply_7(v___x_9302__overap_1148_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, lean_box(0));
return v___x_1149_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v___y_1163_);
return v_res_1170_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1174_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1175_ = lean_unsigned_to_nat(40u);
v___x_1176_ = lean_unsigned_to_nat(49u);
v___x_1177_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1179_ = l_mkPanicMessageWithDecl(v___x_1178_, v___x_1177_, v___x_1176_, v___x_1175_, v___x_1174_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1180_, lean_object* v_e_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_ty_1190_; lean_object* v_body_1191_; uint8_t v___x_1194_; 
v___x_1194_ = l_Lean_Expr_hasFVar(v_e_1181_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_e_1181_);
lean_dec_ref(v_f_1180_);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
else
{
switch(lean_obj_tag(v_e_1181_))
{
case 1:
{
lean_object* v_fvarId_1197_; lean_object* v___x_1198_; 
v_fvarId_1197_ = lean_ctor_get(v_e_1181_, 0);
lean_inc(v_fvarId_1197_);
lean_dec_ref_known(v_e_1181_, 1);
lean_inc(v___y_1187_);
lean_inc_ref(v___y_1186_);
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc(v___y_1182_);
v___x_1198_ = lean_apply_8(v_f_1180_, v_fvarId_1197_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, lean_box(0));
return v___x_1198_;
}
case 2:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref_known(v_e_1181_, 1);
lean_dec_ref(v_f_1180_);
v___x_1199_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1200_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1199_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1200_;
}
case 5:
{
lean_object* v_fn_1201_; lean_object* v_arg_1202_; lean_object* v___x_1203_; 
v_fn_1201_ = lean_ctor_get(v_e_1181_, 0);
lean_inc_ref(v_fn_1201_);
v_arg_1202_ = lean_ctor_get(v_e_1181_, 1);
lean_inc_ref(v_arg_1202_);
lean_dec_ref_known(v_e_1181_, 2);
lean_inc_ref(v_f_1180_);
v___x_1203_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1180_, v_fn_1201_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_dec_ref_known(v___x_1203_, 1);
v_e_1181_ = v_arg_1202_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1202_);
lean_dec_ref(v_f_1180_);
return v___x_1203_;
}
}
case 6:
{
lean_object* v_binderType_1205_; lean_object* v_body_1206_; 
v_binderType_1205_ = lean_ctor_get(v_e_1181_, 1);
lean_inc_ref(v_binderType_1205_);
v_body_1206_ = lean_ctor_get(v_e_1181_, 2);
lean_inc_ref(v_body_1206_);
lean_dec_ref_known(v_e_1181_, 3);
v_ty_1190_ = v_binderType_1205_;
v_body_1191_ = v_body_1206_;
goto v___jp_1189_;
}
case 7:
{
lean_object* v_binderType_1207_; lean_object* v_body_1208_; 
v_binderType_1207_ = lean_ctor_get(v_e_1181_, 1);
lean_inc_ref(v_binderType_1207_);
v_body_1208_ = lean_ctor_get(v_e_1181_, 2);
lean_inc_ref(v_body_1208_);
lean_dec_ref_known(v_e_1181_, 3);
v_ty_1190_ = v_binderType_1207_;
v_body_1191_ = v_body_1208_;
goto v___jp_1189_;
}
case 8:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref_known(v_e_1181_, 4);
lean_dec_ref(v_f_1180_);
v___x_1209_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1210_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1209_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1210_;
}
case 11:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref_known(v_e_1181_, 3);
lean_dec_ref(v_f_1180_);
v___x_1211_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1212_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1211_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1212_;
}
default: 
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v_e_1181_);
lean_dec_ref(v_f_1180_);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
}
v___jp_1189_:
{
lean_object* v___x_1192_; 
lean_inc_ref(v_f_1180_);
v___x_1192_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1180_, v_ty_1190_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec_ref_known(v___x_1192_, 1);
v_e_1181_ = v_body_1191_;
goto _start;
}
else
{
lean_dec_ref(v_body_1191_);
lean_dec_ref(v_f_1180_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1215_, lean_object* v_e_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1215_, v_e_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1225_, lean_object* v_param_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_type_1234_; lean_object* v___x_1235_; 
v_type_1234_ = lean_ctor_get(v_param_1226_, 2);
lean_inc_ref(v_type_1234_);
lean_dec_ref(v_param_1226_);
v___x_1235_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1225_, v_type_1234_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1236_, lean_object* v_param_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1236_, v_param_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1246_, lean_object* v_f_1247_, lean_object* v_as_1248_, size_t v_i_1249_, size_t v_stop_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_usize_dec_eq(v_i_1249_, v_stop_1250_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_array_uget_borrowed(v_as_1248_, v_i_1249_);
lean_inc(v___x_1260_);
lean_inc_ref(v_f_1247_);
v___x_1261_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1247_, v___x_1260_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; size_t v___x_1263_; size_t v___x_1264_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1249_, v___x_1263_);
v_i_1249_ = v___x_1264_;
v_b_1251_ = v_a_1262_;
goto _start;
}
else
{
lean_dec_ref(v_f_1247_);
return v___x_1261_;
}
}
else
{
lean_object* v___x_1266_; 
lean_dec_ref(v_f_1247_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_b_1251_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1267_, lean_object* v_f_1268_, lean_object* v_as_1269_, lean_object* v_i_1270_, lean_object* v_stop_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v_pu_boxed_1280_; size_t v_i_boxed_1281_; size_t v_stop_boxed_1282_; lean_object* v_res_1283_; 
v_pu_boxed_1280_ = lean_unbox(v_pu_1267_);
v_i_boxed_1281_ = lean_unbox_usize(v_i_1270_);
lean_dec(v_i_1270_);
v_stop_boxed_1282_ = lean_unbox_usize(v_stop_1271_);
lean_dec(v_stop_1271_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1280_, v_f_1268_, v_as_1269_, v_i_boxed_1281_, v_stop_boxed_1282_, v_b_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v_as_1269_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1284_, lean_object* v_arg_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
switch(lean_obj_tag(v_arg_1285_))
{
case 0:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v_f_1284_);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
case 1:
{
lean_object* v_fvarId_1295_; lean_object* v___x_1296_; 
v_fvarId_1295_ = lean_ctor_get(v_arg_1285_, 0);
lean_inc(v_fvarId_1295_);
lean_dec_ref_known(v_arg_1285_, 1);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc(v___y_1286_);
v___x_1296_ = lean_apply_8(v_f_1284_, v_fvarId_1295_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
return v___x_1296_;
}
default: 
{
lean_object* v_expr_1297_; lean_object* v___x_1298_; 
v_expr_1297_ = lean_ctor_get(v_arg_1285_, 0);
lean_inc_ref(v_expr_1297_);
lean_dec_ref_known(v_arg_1285_, 1);
v___x_1298_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1284_, v_expr_1297_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1299_, lean_object* v_arg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1299_, v_arg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1309_, lean_object* v_f_1310_, lean_object* v_as_1311_, size_t v_i_1312_, size_t v_stop_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_eq(v_i_1312_, v_stop_1313_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_array_uget_borrowed(v_as_1311_, v_i_1312_);
lean_inc(v___x_1323_);
lean_inc_ref(v_f_1310_);
v___x_1324_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1310_, v___x_1323_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; size_t v___x_1326_; size_t v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_i_1312_, v___x_1326_);
v_i_1312_ = v___x_1327_;
v_b_1314_ = v_a_1325_;
goto _start;
}
else
{
lean_dec_ref(v_f_1310_);
return v___x_1324_;
}
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v_f_1310_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_b_1314_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1330_, lean_object* v_f_1331_, lean_object* v_as_1332_, lean_object* v_i_1333_, lean_object* v_stop_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v_pu_boxed_1343_; size_t v_i_boxed_1344_; size_t v_stop_boxed_1345_; lean_object* v_res_1346_; 
v_pu_boxed_1343_ = lean_unbox(v_pu_1330_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_stop_boxed_1345_ = lean_unbox_usize(v_stop_1334_);
lean_dec(v_stop_1334_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1343_, v_f_1331_, v_as_1332_, v_i_boxed_1344_, v_stop_boxed_1345_, v_b_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v_as_1332_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1347_, lean_object* v_f_1348_, lean_object* v_e_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_args_1358_; 
switch(lean_obj_tag(v_e_1349_))
{
case 2:
{
lean_object* v_struct_1372_; lean_object* v___x_1373_; 
v_struct_1372_ = lean_ctor_get(v_e_1349_, 2);
lean_inc(v_struct_1372_);
lean_dec_ref_known(v_e_1349_, 3);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1373_ = lean_apply_8(v_f_1348_, v_struct_1372_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1373_;
}
case 3:
{
lean_object* v_args_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_args_1374_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_args_1374_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_array_get_size(v_args_1374_);
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_nat_dec_lt(v___x_1375_, v___x_1376_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_args_1374_);
lean_dec_ref(v_f_1348_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
return v___x_1379_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_le(v___x_1376_, v___x_1376_);
if (v___x_1380_ == 0)
{
if (v___x_1378_ == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref(v_args_1374_);
lean_dec_ref(v_f_1348_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1377_);
return v___x_1381_;
}
else
{
size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1376_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1374_, v___x_1382_, v___x_1383_, v___x_1377_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1374_);
return v___x_1384_;
}
}
else
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = lean_usize_of_nat(v___x_1376_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1374_, v___x_1385_, v___x_1386_, v___x_1377_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1374_);
return v___x_1387_;
}
}
}
case 4:
{
lean_object* v_fvarId_1388_; lean_object* v_args_1389_; lean_object* v___x_1390_; 
v_fvarId_1388_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_fvarId_1388_);
v_args_1389_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1389_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc_ref(v_f_1348_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1390_ = lean_apply_8(v_f_1348_, v_fvarId_1388_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1411_; 
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1390_, 0);
lean_dec(v_unused_1412_);
v___x_1392_ = v___x_1390_;
v_isShared_1393_ = v_isSharedCheck_1411_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v___x_1390_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1411_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = lean_array_get_size(v_args_1389_);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_nat_dec_lt(v___x_1394_, v___x_1395_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref(v_args_1389_);
lean_dec_ref(v_f_1348_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1396_);
v___x_1399_ = v___x_1392_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1396_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_nat_dec_le(v___x_1395_, v___x_1395_);
if (v___x_1401_ == 0)
{
if (v___x_1397_ == 0)
{
lean_object* v___x_1403_; 
lean_dec_ref(v_args_1389_);
lean_dec_ref(v_f_1348_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1396_);
v___x_1403_ = v___x_1392_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1396_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
size_t v___x_1405_; size_t v___x_1406_; lean_object* v___x_1407_; 
lean_del_object(v___x_1392_);
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = lean_usize_of_nat(v___x_1395_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1389_, v___x_1405_, v___x_1406_, v___x_1396_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1389_);
return v___x_1407_;
}
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
lean_del_object(v___x_1392_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1395_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1389_, v___x_1408_, v___x_1409_, v___x_1396_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1389_);
return v___x_1410_;
}
}
}
}
else
{
lean_dec_ref(v_args_1389_);
lean_dec_ref(v_f_1348_);
return v___x_1390_;
}
}
case 5:
{
lean_object* v_args_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_args_1413_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1413_);
lean_dec_ref_known(v_e_1349_, 2);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_args_1413_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_args_1413_);
lean_dec_ref(v_f_1348_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
return v___x_1418_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_le(v___x_1415_, v___x_1415_);
if (v___x_1419_ == 0)
{
if (v___x_1417_ == 0)
{
lean_object* v___x_1420_; 
lean_dec_ref(v_args_1413_);
lean_dec_ref(v_f_1348_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1416_);
return v___x_1420_;
}
else
{
size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = lean_usize_of_nat(v___x_1415_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1413_, v___x_1421_, v___x_1422_, v___x_1416_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1413_);
return v___x_1423_;
}
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1415_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1413_, v___x_1424_, v___x_1425_, v___x_1416_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1413_);
return v___x_1426_;
}
}
}
case 6:
{
lean_object* v_var_1427_; lean_object* v___x_1428_; 
v_var_1427_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_var_1427_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1428_ = lean_apply_8(v_f_1348_, v_var_1427_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1428_;
}
case 7:
{
lean_object* v_var_1429_; lean_object* v___x_1430_; 
v_var_1429_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_var_1429_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1430_ = lean_apply_8(v_f_1348_, v_var_1429_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1430_;
}
case 8:
{
lean_object* v_var_1431_; lean_object* v___x_1432_; 
v_var_1431_ = lean_ctor_get(v_e_1349_, 2);
lean_inc(v_var_1431_);
lean_dec_ref_known(v_e_1349_, 3);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1432_ = lean_apply_8(v_f_1348_, v_var_1431_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1432_;
}
case 9:
{
lean_object* v_args_1433_; 
v_args_1433_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1433_);
lean_dec_ref_known(v_e_1349_, 2);
v_args_1358_ = v_args_1433_;
goto v___jp_1357_;
}
case 10:
{
lean_object* v_args_1434_; 
v_args_1434_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1434_);
lean_dec_ref_known(v_e_1349_, 2);
v_args_1358_ = v_args_1434_;
goto v___jp_1357_;
}
case 11:
{
lean_object* v_var_1435_; lean_object* v___x_1436_; 
v_var_1435_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_var_1435_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1436_ = lean_apply_8(v_f_1348_, v_var_1435_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1436_;
}
case 12:
{
lean_object* v_var_1437_; lean_object* v_args_1438_; lean_object* v___x_1439_; 
v_var_1437_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_var_1437_);
v_args_1438_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_args_1438_);
lean_dec_ref_known(v_e_1349_, 3);
lean_inc_ref(v_f_1348_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1439_ = lean_apply_8(v_f_1348_, v_var_1437_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1460_; 
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1461_);
v___x_1441_ = v___x_1439_;
v_isShared_1442_ = v_isSharedCheck_1460_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v___x_1439_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1460_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_array_get_size(v_args_1438_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_nat_dec_lt(v___x_1443_, v___x_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref(v_args_1438_);
lean_dec_ref(v_f_1348_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1445_);
v___x_1448_ = v___x_1441_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1445_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
else
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_nat_dec_le(v___x_1444_, v___x_1444_);
if (v___x_1450_ == 0)
{
if (v___x_1446_ == 0)
{
lean_object* v___x_1452_; 
lean_dec_ref(v_args_1438_);
lean_dec_ref(v_f_1348_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1445_);
v___x_1452_ = v___x_1441_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1445_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
lean_del_object(v___x_1441_);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = lean_usize_of_nat(v___x_1444_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1438_, v___x_1454_, v___x_1455_, v___x_1445_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1438_);
return v___x_1456_;
}
}
else
{
size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
lean_del_object(v___x_1441_);
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = lean_usize_of_nat(v___x_1444_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1438_, v___x_1457_, v___x_1458_, v___x_1445_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1438_);
return v___x_1459_;
}
}
}
}
else
{
lean_dec_ref(v_args_1438_);
lean_dec_ref(v_f_1348_);
return v___x_1439_;
}
}
case 13:
{
lean_object* v_fvarId_1462_; lean_object* v___x_1463_; 
v_fvarId_1462_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_fvarId_1462_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1463_ = lean_apply_8(v_f_1348_, v_fvarId_1462_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1463_;
}
case 14:
{
lean_object* v_fvarId_1464_; lean_object* v___x_1465_; 
v_fvarId_1464_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_fvarId_1464_);
lean_dec_ref_known(v_e_1349_, 1);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1465_ = lean_apply_8(v_f_1348_, v_fvarId_1464_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1465_;
}
case 15:
{
lean_object* v_fvarId_1466_; lean_object* v___x_1467_; 
v_fvarId_1466_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_fvarId_1466_);
lean_dec_ref_known(v_e_1349_, 1);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1467_ = lean_apply_8(v_f_1348_, v_fvarId_1466_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1467_;
}
default: 
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v_e_1349_);
lean_dec_ref(v_f_1348_);
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
v___jp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_array_get_size(v_args_1358_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_nat_dec_lt(v___x_1359_, v___x_1360_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref(v_args_1358_);
lean_dec_ref(v_f_1348_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
return v___x_1363_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_nat_dec_le(v___x_1360_, v___x_1360_);
if (v___x_1364_ == 0)
{
if (v___x_1362_ == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref(v_args_1358_);
lean_dec_ref(v_f_1348_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1361_);
return v___x_1365_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = lean_usize_of_nat(v___x_1360_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1358_, v___x_1366_, v___x_1367_, v___x_1361_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1358_);
return v___x_1368_;
}
}
else
{
size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1360_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1358_, v___x_1369_, v___x_1370_, v___x_1361_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1358_);
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1470_, lean_object* v_f_1471_, lean_object* v_e_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v_pu_boxed_1480_; lean_object* v_res_1481_; 
v_pu_boxed_1480_ = lean_unbox(v_pu_1470_);
v_res_1481_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1480_, v_f_1471_, v_e_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1482_, lean_object* v_f_1483_, lean_object* v_decl_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_type_1492_; lean_object* v_value_1493_; lean_object* v___x_1494_; 
v_type_1492_ = lean_ctor_get(v_decl_1484_, 2);
lean_inc_ref(v_type_1492_);
v_value_1493_ = lean_ctor_get(v_decl_1484_, 3);
lean_inc(v_value_1493_);
lean_dec_ref(v_decl_1484_);
lean_inc_ref(v_f_1483_);
v___x_1494_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1483_, v_type_1492_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref_known(v___x_1494_, 1);
v___x_1495_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1482_, v_f_1483_, v_value_1493_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1495_;
}
else
{
lean_dec(v_value_1493_);
lean_dec_ref(v_f_1483_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1496_, lean_object* v_f_1497_, lean_object* v_decl_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v_pu_boxed_1506_; lean_object* v_res_1507_; 
v_pu_boxed_1506_ = lean_unbox(v_pu_1496_);
v_res_1507_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1506_, v_f_1497_, v_decl_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1508_, lean_object* v_f_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v_pu_boxed_1518_; lean_object* v_res_1519_; 
v_pu_boxed_1518_ = lean_unbox(v_pu_1508_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1518_, v_f_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec(v___y_1511_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1520_, lean_object* v_f_1521_, lean_object* v_as_1522_, size_t v_i_1523_, size_t v_stop_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_usize_dec_eq(v_i_1523_, v_stop_1524_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1534_ = lean_box(v_pu_1520_);
lean_inc_ref(v_f_1521_);
v___f_1535_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1535_, 0, v___x_1534_);
lean_closure_set(v___f_1535_, 1, v_f_1521_);
v___x_1536_ = lean_array_uget_borrowed(v_as_1522_, v_i_1523_);
lean_inc(v___x_1536_);
v___x_1537_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1536_, v___f_1535_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; size_t v___x_1539_; size_t v___x_1540_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1523_, v___x_1539_);
v_i_1523_ = v___x_1540_;
v_b_1525_ = v_a_1538_;
goto _start;
}
else
{
lean_dec_ref(v_f_1521_);
return v___x_1537_;
}
}
else
{
lean_object* v___x_1542_; 
lean_dec_ref(v_f_1521_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_b_1525_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1543_, lean_object* v_f_1544_, lean_object* v_c_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
switch(lean_obj_tag(v_c_1545_))
{
case 0:
{
lean_object* v_decl_1553_; lean_object* v_k_1554_; lean_object* v___x_1555_; 
v_decl_1553_ = lean_ctor_get(v_c_1545_, 0);
lean_inc_ref(v_decl_1553_);
v_k_1554_ = lean_ctor_get(v_c_1545_, 1);
lean_inc_ref(v_k_1554_);
lean_dec_ref_known(v_c_1545_, 2);
lean_inc_ref(v_f_1544_);
v___x_1555_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1543_, v_f_1544_, v_decl_1553_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_dec_ref_known(v___x_1555_, 1);
v_c_1545_ = v_k_1554_;
goto _start;
}
else
{
lean_dec_ref(v_k_1554_);
lean_dec_ref(v_f_1544_);
return v___x_1555_;
}
}
case 3:
{
lean_object* v_fvarId_1557_; lean_object* v_args_1558_; lean_object* v___x_1559_; 
v_fvarId_1557_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1557_);
v_args_1558_ = lean_ctor_get(v_c_1545_, 1);
lean_inc_ref(v_args_1558_);
lean_dec_ref_known(v_c_1545_, 2);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1559_ = lean_apply_8(v_f_1544_, v_fvarId_1557_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1559_, 0);
lean_dec(v_unused_1581_);
v___x_1561_ = v___x_1559_;
v_isShared_1562_ = v_isSharedCheck_1580_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v___x_1559_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1580_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_array_get_size(v_args_1558_);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref(v_args_1558_);
lean_dec_ref(v_f_1544_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1565_);
v___x_1568_ = v___x_1561_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1565_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
else
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_nat_dec_le(v___x_1564_, v___x_1564_);
if (v___x_1570_ == 0)
{
if (v___x_1566_ == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref(v_args_1558_);
lean_dec_ref(v_f_1544_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1565_);
v___x_1572_ = v___x_1561_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1565_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
lean_del_object(v___x_1561_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = lean_usize_of_nat(v___x_1564_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1543_, v_f_1544_, v_args_1558_, v___x_1574_, v___x_1575_, v___x_1565_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_args_1558_);
return v___x_1576_;
}
}
else
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1561_);
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = lean_usize_of_nat(v___x_1564_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1543_, v_f_1544_, v_args_1558_, v___x_1577_, v___x_1578_, v___x_1565_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_args_1558_);
return v___x_1579_;
}
}
}
}
else
{
lean_dec_ref(v_args_1558_);
lean_dec_ref(v_f_1544_);
return v___x_1559_;
}
}
case 4:
{
lean_object* v_cases_1582_; lean_object* v_resultType_1583_; lean_object* v_discr_1584_; lean_object* v_alts_1585_; lean_object* v___x_1586_; 
v_cases_1582_ = lean_ctor_get(v_c_1545_, 0);
lean_inc_ref(v_cases_1582_);
lean_dec_ref_known(v_c_1545_, 1);
v_resultType_1583_ = lean_ctor_get(v_cases_1582_, 1);
lean_inc_ref(v_resultType_1583_);
v_discr_1584_ = lean_ctor_get(v_cases_1582_, 2);
lean_inc(v_discr_1584_);
v_alts_1585_ = lean_ctor_get(v_cases_1582_, 3);
lean_inc_ref(v_alts_1585_);
lean_dec_ref(v_cases_1582_);
lean_inc_ref(v_f_1544_);
v___x_1586_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1544_, v_resultType_1583_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref_known(v___x_1586_, 1);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1587_ = lean_apply_8(v_f_1544_, v_discr_1584_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1608_; 
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1587_, 0);
lean_dec(v_unused_1609_);
v___x_1589_ = v___x_1587_;
v_isShared_1590_ = v_isSharedCheck_1608_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v___x_1587_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1608_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_array_get_size(v_alts_1585_);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_nat_dec_lt(v___x_1591_, v___x_1592_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref(v_alts_1585_);
lean_dec_ref(v_f_1544_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1593_);
v___x_1596_ = v___x_1589_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1593_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_nat_dec_le(v___x_1592_, v___x_1592_);
if (v___x_1598_ == 0)
{
if (v___x_1594_ == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref(v_alts_1585_);
lean_dec_ref(v_f_1544_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1593_);
v___x_1600_ = v___x_1589_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1593_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
lean_del_object(v___x_1589_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = lean_usize_of_nat(v___x_1592_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1543_, v_f_1544_, v_alts_1585_, v___x_1602_, v___x_1603_, v___x_1593_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_alts_1585_);
return v___x_1604_;
}
}
else
{
size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1589_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = lean_usize_of_nat(v___x_1592_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1543_, v_f_1544_, v_alts_1585_, v___x_1605_, v___x_1606_, v___x_1593_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_alts_1585_);
return v___x_1607_;
}
}
}
}
else
{
lean_dec_ref(v_alts_1585_);
lean_dec_ref(v_f_1544_);
return v___x_1587_;
}
}
else
{
lean_dec_ref(v_alts_1585_);
lean_dec(v_discr_1584_);
lean_dec_ref(v_f_1544_);
return v___x_1586_;
}
}
case 5:
{
lean_object* v_fvarId_1610_; lean_object* v___x_1611_; 
v_fvarId_1610_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1610_);
lean_dec_ref_known(v_c_1545_, 1);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1611_ = lean_apply_8(v_f_1544_, v_fvarId_1610_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
return v___x_1611_;
}
case 6:
{
lean_object* v_type_1612_; lean_object* v___x_1613_; 
v_type_1612_ = lean_ctor_get(v_c_1545_, 0);
lean_inc_ref(v_type_1612_);
lean_dec_ref_known(v_c_1545_, 1);
v___x_1613_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1544_, v_type_1612_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1613_;
}
case 7:
{
lean_object* v_fvarId_1614_; lean_object* v_y_1615_; lean_object* v_k_1616_; lean_object* v___x_1617_; 
v_fvarId_1614_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1614_);
v_y_1615_ = lean_ctor_get(v_c_1545_, 2);
lean_inc(v_y_1615_);
v_k_1616_ = lean_ctor_get(v_c_1545_, 3);
lean_inc_ref(v_k_1616_);
lean_dec_ref_known(v_c_1545_, 4);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1617_ = lean_apply_8(v_f_1544_, v_fvarId_1614_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref_known(v___x_1617_, 1);
lean_inc_ref(v_f_1544_);
v___x_1618_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1544_, v_y_1615_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
v_c_1545_ = v_k_1616_;
goto _start;
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_f_1544_);
return v___x_1618_;
}
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec(v_y_1615_);
lean_dec_ref(v_f_1544_);
return v___x_1617_;
}
}
case 8:
{
lean_object* v_fvarId_1620_; lean_object* v_y_1621_; lean_object* v_k_1622_; lean_object* v___x_1623_; 
v_fvarId_1620_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1620_);
v_y_1621_ = lean_ctor_get(v_c_1545_, 2);
lean_inc(v_y_1621_);
v_k_1622_ = lean_ctor_get(v_c_1545_, 3);
lean_inc_ref(v_k_1622_);
lean_dec_ref_known(v_c_1545_, 4);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1623_ = lean_apply_8(v_f_1544_, v_fvarId_1620_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1624_; 
lean_dec_ref_known(v___x_1623_, 1);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1624_ = lean_apply_8(v_f_1544_, v_y_1621_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref_known(v___x_1624_, 1);
v_c_1545_ = v_k_1622_;
goto _start;
}
else
{
lean_dec_ref(v_k_1622_);
lean_dec_ref(v_f_1544_);
return v___x_1624_;
}
}
else
{
lean_dec_ref(v_k_1622_);
lean_dec(v_y_1621_);
lean_dec_ref(v_f_1544_);
return v___x_1623_;
}
}
case 9:
{
lean_object* v_fvarId_1626_; lean_object* v_y_1627_; lean_object* v_ty_1628_; lean_object* v_k_1629_; lean_object* v___x_1630_; 
v_fvarId_1626_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1626_);
v_y_1627_ = lean_ctor_get(v_c_1545_, 3);
lean_inc(v_y_1627_);
v_ty_1628_ = lean_ctor_get(v_c_1545_, 4);
lean_inc_ref(v_ty_1628_);
v_k_1629_ = lean_ctor_get(v_c_1545_, 5);
lean_inc_ref(v_k_1629_);
lean_dec_ref_known(v_c_1545_, 6);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1630_ = lean_apply_8(v_f_1544_, v_fvarId_1626_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref_known(v___x_1630_, 1);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1631_ = lean_apply_8(v_f_1544_, v_y_1627_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1631_, 1);
lean_inc_ref(v_f_1544_);
v___x_1632_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1544_, v_ty_1628_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_dec_ref_known(v___x_1632_, 1);
v_c_1545_ = v_k_1629_;
goto _start;
}
else
{
lean_dec_ref(v_k_1629_);
lean_dec_ref(v_f_1544_);
return v___x_1632_;
}
}
else
{
lean_dec_ref(v_k_1629_);
lean_dec_ref(v_ty_1628_);
lean_dec_ref(v_f_1544_);
return v___x_1631_;
}
}
else
{
lean_dec_ref(v_k_1629_);
lean_dec_ref(v_ty_1628_);
lean_dec(v_y_1627_);
lean_dec_ref(v_f_1544_);
return v___x_1630_;
}
}
case 10:
{
lean_object* v_fvarId_1634_; lean_object* v_k_1635_; lean_object* v___x_1636_; 
v_fvarId_1634_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1634_);
v_k_1635_ = lean_ctor_get(v_c_1545_, 2);
lean_inc_ref(v_k_1635_);
lean_dec_ref_known(v_c_1545_, 3);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1636_ = lean_apply_8(v_f_1544_, v_fvarId_1634_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_dec_ref_known(v___x_1636_, 1);
v_c_1545_ = v_k_1635_;
goto _start;
}
else
{
lean_dec_ref(v_k_1635_);
lean_dec_ref(v_f_1544_);
return v___x_1636_;
}
}
case 11:
{
lean_object* v_fvarId_1638_; lean_object* v_k_1639_; lean_object* v___x_1640_; 
v_fvarId_1638_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1638_);
v_k_1639_ = lean_ctor_get(v_c_1545_, 2);
lean_inc_ref(v_k_1639_);
lean_dec_ref_known(v_c_1545_, 3);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1640_ = lean_apply_8(v_f_1544_, v_fvarId_1638_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec_ref_known(v___x_1640_, 1);
v_c_1545_ = v_k_1639_;
goto _start;
}
else
{
lean_dec_ref(v_k_1639_);
lean_dec_ref(v_f_1544_);
return v___x_1640_;
}
}
case 12:
{
lean_object* v_fvarId_1642_; lean_object* v_k_1643_; lean_object* v___x_1644_; 
v_fvarId_1642_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1642_);
v_k_1643_ = lean_ctor_get(v_c_1545_, 3);
lean_inc_ref(v_k_1643_);
lean_dec_ref_known(v_c_1545_, 4);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1644_ = lean_apply_8(v_f_1544_, v_fvarId_1642_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_dec_ref_known(v___x_1644_, 1);
v_c_1545_ = v_k_1643_;
goto _start;
}
else
{
lean_dec_ref(v_k_1643_);
lean_dec_ref(v_f_1544_);
return v___x_1644_;
}
}
case 13:
{
lean_object* v_fvarId_1646_; lean_object* v_k_1647_; lean_object* v___x_1648_; 
v_fvarId_1646_ = lean_ctor_get(v_c_1545_, 0);
lean_inc(v_fvarId_1646_);
v_k_1647_ = lean_ctor_get(v_c_1545_, 1);
lean_inc_ref(v_k_1647_);
lean_dec_ref_known(v_c_1545_, 2);
lean_inc_ref(v_f_1544_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc(v___y_1546_);
v___x_1648_ = lean_apply_8(v_f_1544_, v_fvarId_1646_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_dec_ref_known(v___x_1648_, 1);
v_c_1545_ = v_k_1647_;
goto _start;
}
else
{
lean_dec_ref(v_k_1647_);
lean_dec_ref(v_f_1544_);
return v___x_1648_;
}
}
default: 
{
lean_object* v_decl_1650_; lean_object* v_k_1651_; lean_object* v_params_1652_; lean_object* v_type_1653_; lean_object* v_value_1654_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_decl_1650_ = lean_ctor_get(v_c_1545_, 0);
lean_inc_ref(v_decl_1650_);
v_k_1651_ = lean_ctor_get(v_c_1545_, 1);
lean_inc_ref(v_k_1651_);
lean_dec_ref(v_c_1545_);
v_params_1652_ = lean_ctor_get(v_decl_1650_, 2);
lean_inc_ref(v_params_1652_);
v_type_1653_ = lean_ctor_get(v_decl_1650_, 3);
lean_inc_ref(v_type_1653_);
v_value_1654_ = lean_ctor_get(v_decl_1650_, 4);
lean_inc_ref(v_value_1654_);
lean_dec_ref(v_decl_1650_);
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_array_get_size(v_params_1652_);
v___x_1667_ = lean_nat_dec_lt(v___x_1665_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref(v_params_1652_);
lean_inc_ref(v_f_1544_);
v___x_1668_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1544_, v_type_1653_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref_known(v___x_1668_, 1);
lean_inc_ref(v_f_1544_);
v___x_1669_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1543_, v_f_1544_, v_value_1654_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_dec_ref_known(v___x_1669_, 1);
v_c_1545_ = v_k_1651_;
goto _start;
}
else
{
lean_dec_ref(v_k_1651_);
lean_dec_ref(v_f_1544_);
return v___x_1669_;
}
}
else
{
lean_dec_ref(v_value_1654_);
lean_dec_ref(v_k_1651_);
lean_dec_ref(v_f_1544_);
return v___x_1668_;
}
}
else
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_nat_dec_le(v___x_1666_, v___x_1666_);
if (v___x_1672_ == 0)
{
if (v___x_1667_ == 0)
{
lean_dec_ref(v_params_1652_);
v___y_1656_ = v___y_1546_;
v___y_1657_ = v___y_1547_;
v___y_1658_ = v___y_1548_;
v___y_1659_ = v___y_1549_;
v___y_1660_ = v___y_1550_;
v___y_1661_ = v___y_1551_;
goto v___jp_1655_;
}
else
{
size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = lean_usize_of_nat(v___x_1666_);
lean_inc_ref(v_f_1544_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1543_, v_f_1544_, v_params_1652_, v___x_1673_, v___x_1674_, v___x_1671_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_params_1652_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_dec_ref_known(v___x_1675_, 1);
v___y_1656_ = v___y_1546_;
v___y_1657_ = v___y_1547_;
v___y_1658_ = v___y_1548_;
v___y_1659_ = v___y_1549_;
v___y_1660_ = v___y_1550_;
v___y_1661_ = v___y_1551_;
goto v___jp_1655_;
}
else
{
lean_dec_ref(v_value_1654_);
lean_dec_ref(v_type_1653_);
lean_dec_ref(v_k_1651_);
lean_dec_ref(v_f_1544_);
return v___x_1675_;
}
}
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_of_nat(v___x_1666_);
lean_inc_ref(v_f_1544_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1543_, v_f_1544_, v_params_1652_, v___x_1676_, v___x_1677_, v___x_1671_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_params_1652_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref_known(v___x_1678_, 1);
v___y_1656_ = v___y_1546_;
v___y_1657_ = v___y_1547_;
v___y_1658_ = v___y_1548_;
v___y_1659_ = v___y_1549_;
v___y_1660_ = v___y_1550_;
v___y_1661_ = v___y_1551_;
goto v___jp_1655_;
}
else
{
lean_dec_ref(v_value_1654_);
lean_dec_ref(v_type_1653_);
lean_dec_ref(v_k_1651_);
lean_dec_ref(v_f_1544_);
return v___x_1678_;
}
}
}
v___jp_1655_:
{
lean_object* v___x_1662_; 
lean_inc_ref(v_f_1544_);
v___x_1662_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1544_, v_type_1653_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref_known(v___x_1662_, 1);
lean_inc_ref(v_f_1544_);
v___x_1663_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1543_, v_f_1544_, v_value_1654_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec_ref_known(v___x_1663_, 1);
v_c_1545_ = v_k_1651_;
v___y_1546_ = v___y_1656_;
v___y_1547_ = v___y_1657_;
v___y_1548_ = v___y_1658_;
v___y_1549_ = v___y_1659_;
v___y_1550_ = v___y_1660_;
v___y_1551_ = v___y_1661_;
goto _start;
}
else
{
lean_dec_ref(v_k_1651_);
lean_dec_ref(v_f_1544_);
return v___x_1663_;
}
}
else
{
lean_dec_ref(v_value_1654_);
lean_dec_ref(v_k_1651_);
lean_dec_ref(v_f_1544_);
return v___x_1662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1679_, lean_object* v_f_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1679_, v_f_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1690_, lean_object* v_f_1691_, lean_object* v_as_1692_, lean_object* v_i_1693_, lean_object* v_stop_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
uint8_t v_pu_boxed_1703_; size_t v_i_boxed_1704_; size_t v_stop_boxed_1705_; lean_object* v_res_1706_; 
v_pu_boxed_1703_ = lean_unbox(v_pu_1690_);
v_i_boxed_1704_ = lean_unbox_usize(v_i_1693_);
lean_dec(v_i_1693_);
v_stop_boxed_1705_ = lean_unbox_usize(v_stop_1694_);
lean_dec(v_stop_1694_);
v_res_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1703_, v_f_1691_, v_as_1692_, v_i_boxed_1704_, v_stop_boxed_1705_, v_b_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_as_1692_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1707_, lean_object* v_f_1708_, lean_object* v_c_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v_pu_boxed_1717_; lean_object* v_res_1718_; 
v_pu_boxed_1717_ = lean_unbox(v_pu_1707_);
v_res_1718_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1717_, v_f_1708_, v_c_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1719_, lean_object* v_as_1720_, size_t v_i_1721_, size_t v_stop_1722_, lean_object* v_b_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_eq(v_i_1721_, v_stop_1722_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_inc(v___x_1719_);
v___x_1732_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1732_, 0, v___x_1719_);
v___x_1733_ = lean_array_uget_borrowed(v_as_1720_, v_i_1721_);
lean_inc(v___x_1733_);
v___x_1734_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1732_, v___x_1733_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; size_t v___x_1736_; size_t v___x_1737_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_add(v_i_1721_, v___x_1736_);
v_i_1721_ = v___x_1737_;
v_b_1723_ = v_a_1735_;
goto _start;
}
else
{
lean_dec(v___x_1719_);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v___x_1719_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1723_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1740_, lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_stop_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
size_t v_i_boxed_1752_; size_t v_stop_boxed_1753_; lean_object* v_res_1754_; 
v_i_boxed_1752_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_stop_boxed_1753_ = lean_unbox_usize(v_stop_1743_);
lean_dec(v_stop_1743_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1740_, v_as_1741_, v_i_boxed_1752_, v_stop_boxed_1753_, v_b_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v_as_1741_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = 0;
v___x_1764_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1755_);
lean_inc(v___x_1764_);
v___x_1765_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1765_, 0, v___x_1764_);
switch(lean_obj_tag(v_alt_1755_))
{
case 0:
{
lean_object* v_params_1766_; lean_object* v_code_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_params_1766_ = lean_ctor_get(v_alt_1755_, 1);
lean_inc_ref(v_params_1766_);
v_code_1767_ = lean_ctor_get(v_alt_1755_, 2);
lean_inc_ref(v_code_1767_);
lean_dec_ref_known(v_alt_1755_, 3);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_array_get_size(v_params_1766_);
v___x_1770_ = lean_nat_dec_lt(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_params_1766_);
lean_dec(v___x_1764_);
v___x_1771_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1763_, v___x_1765_, v_code_1767_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_nat_dec_le(v___x_1769_, v___x_1769_);
if (v___x_1773_ == 0)
{
if (v___x_1770_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v_params_1766_);
lean_dec(v___x_1764_);
v___x_1774_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1763_, v___x_1765_, v_code_1767_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1774_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = lean_usize_of_nat(v___x_1769_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1764_, v_params_1766_, v___x_1775_, v___x_1776_, v___x_1772_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec_ref(v_params_1766_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v___x_1777_, 1);
v___x_1778_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1763_, v___x_1765_, v_code_1767_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1778_;
}
else
{
lean_dec_ref(v_code_1767_);
lean_dec_ref(v___x_1765_);
return v___x_1777_;
}
}
}
else
{
size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = ((size_t)0ULL);
v___x_1780_ = lean_usize_of_nat(v___x_1769_);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1764_, v_params_1766_, v___x_1779_, v___x_1780_, v___x_1772_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec_ref(v_params_1766_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1782_; 
lean_dec_ref_known(v___x_1781_, 1);
v___x_1782_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1763_, v___x_1765_, v_code_1767_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1782_;
}
else
{
lean_dec_ref(v_code_1767_);
lean_dec_ref(v___x_1765_);
return v___x_1781_;
}
}
}
}
case 1:
{
lean_object* v_code_1783_; lean_object* v___x_1784_; 
lean_dec(v___x_1764_);
v_code_1783_ = lean_ctor_get(v_alt_1755_, 1);
lean_inc_ref(v_code_1783_);
lean_dec_ref_known(v_alt_1755_, 2);
v___x_1784_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1763_, v___x_1765_, v_code_1783_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1784_;
}
default: 
{
lean_object* v_code_1785_; lean_object* v___x_1786_; 
lean_dec(v___x_1764_);
v_code_1785_ = lean_ctor_get(v_alt_1755_, 0);
lean_inc_ref(v_code_1785_);
lean_dec_ref_known(v_alt_1755_, 1);
v___x_1786_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1763_, v___x_1765_, v_code_1785_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec(v_a_1788_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1796_, lean_object* v_f_1797_, lean_object* v_param_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1797_, v_param_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1807_, lean_object* v_f_1808_, lean_object* v_param_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v_pu_boxed_1817_; lean_object* v_res_1818_; 
v_pu_boxed_1817_ = lean_unbox(v_pu_1807_);
v_res_1818_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1817_, v_f_1808_, v_param_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1819_, lean_object* v_alt_1820_, lean_object* v_f_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1820_, v_f_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1830_, lean_object* v_alt_1831_, lean_object* v_f_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_pu_boxed_1840_; lean_object* v_res_1841_; 
v_pu_boxed_1840_ = lean_unbox(v_pu_1830_);
v_res_1841_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1840_, v_alt_1831_, v_f_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec(v___y_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1842_, lean_object* v_f_1843_, lean_object* v_arg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1843_, v_arg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1853_, lean_object* v_f_1854_, lean_object* v_arg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_pu_boxed_1863_; lean_object* v_res_1864_; 
v_pu_boxed_1863_ = lean_unbox(v_pu_1853_);
v_res_1864_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1863_, v_f_1854_, v_arg_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1865_, size_t v_i_1866_, size_t v_stop_1867_, lean_object* v_b_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_usize_dec_eq(v_i_1866_, v_stop_1867_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_array_uget_borrowed(v_as_1865_, v_i_1866_);
lean_inc(v___x_1877_);
v___x_1878_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1877_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; size_t v___x_1880_; size_t v___x_1881_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = ((size_t)1ULL);
v___x_1881_ = lean_usize_add(v_i_1866_, v___x_1880_);
v_i_1866_ = v___x_1881_;
v_b_1868_ = v_a_1879_;
goto _start;
}
else
{
return v___x_1878_;
}
}
else
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_b_1868_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1884_, lean_object* v_i_1885_, lean_object* v_stop_1886_, lean_object* v_b_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
size_t v_i_boxed_1895_; size_t v_stop_boxed_1896_; lean_object* v_res_1897_; 
v_i_boxed_1895_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_stop_boxed_1896_ = lean_unbox_usize(v_stop_1886_);
lean_dec(v_stop_1886_);
v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1884_, v_i_boxed_1895_, v_stop_boxed_1896_, v_b_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v_as_1884_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_alts_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_alts_1906_ = lean_ctor_get(v_cs_1898_, 3);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_array_get_size(v_alts_1906_);
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_nat_dec_lt(v___x_1907_, v___x_1908_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
return v___x_1911_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_le(v___x_1908_, v___x_1908_);
if (v___x_1912_ == 0)
{
if (v___x_1910_ == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1909_);
return v___x_1913_;
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1908_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1906_, v___x_1914_, v___x_1915_, v___x_1909_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
return v___x_1916_;
}
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = lean_usize_of_nat(v___x_1908_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1906_, v___x_1917_, v___x_1918_, v___x_1909_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_cs_1920_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
if (lean_obj_tag(v_x_1930_) == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_x_1929_);
return v___x_1936_;
}
else
{
lean_object* v_head_1937_; lean_object* v_tail_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_2000_; 
v_head_1937_ = lean_ctor_get(v_x_1930_, 0);
v_tail_1938_ = lean_ctor_get(v_x_1930_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1930_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1940_ = v_x_1930_;
v_isShared_1941_ = v_isSharedCheck_2000_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_tail_1938_);
lean_inc(v_head_1937_);
lean_dec(v_x_1930_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_2000_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1999_; 
v_fst_1942_ = lean_ctor_get(v_x_1929_, 0);
v_snd_1943_ = lean_ctor_get(v_x_1929_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_x_1929_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1945_ = v_x_1929_;
v_isShared_1946_ = v_isSharedCheck_1999_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_inc(v_fst_1942_);
lean_dec(v_x_1929_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1999_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; 
if (lean_obj_tag(v_head_1937_) == 0)
{
lean_object* v_decl_1980_; lean_object* v___x_1981_; 
v_decl_1980_ = lean_ctor_get(v_head_1937_, 0);
lean_inc_ref(v_decl_1980_);
v___x_1981_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_1980_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; uint8_t v___x_1983_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = lean_unbox(v_a_1982_);
lean_dec(v_a_1982_);
if (v___x_1983_ == 0)
{
lean_del_object(v___x_1940_);
v___y_1948_ = v___y_1931_;
v___y_1949_ = v___y_1932_;
v___y_1950_ = v___y_1933_;
v___y_1951_ = v___y_1934_;
goto v___jp_1947_;
}
else
{
lean_object* v_fvarId_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_inc_ref(v_decl_1980_);
lean_dec_ref_known(v_head_1937_, 1);
lean_del_object(v___x_1945_);
v_fvarId_1984_ = lean_ctor_get(v_decl_1980_, 0);
lean_inc(v_fvarId_1984_);
lean_dec_ref(v_decl_1980_);
v___x_1985_ = lean_box(2);
v___x_1986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1942_, v_fvarId_1984_, v___x_1985_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 0);
lean_ctor_set(v___x_1940_, 1, v_snd_1943_);
lean_ctor_set(v___x_1940_, 0, v___x_1986_);
v___x_1988_ = v___x_1940_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_snd_1943_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v_x_1929_ = v___x_1988_;
v_x_1930_ = v_tail_1938_;
goto _start;
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref_known(v_head_1937_, 1);
lean_del_object(v___x_1945_);
lean_dec(v_snd_1943_);
lean_dec(v_fst_1942_);
lean_del_object(v___x_1940_);
lean_dec(v_tail_1938_);
v_a_1991_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1981_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1981_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_del_object(v___x_1940_);
v___y_1948_ = v___y_1931_;
v___y_1949_ = v___y_1932_;
v___y_1950_ = v___y_1933_;
v___y_1951_ = v___y_1934_;
goto v___jp_1947_;
}
v___jp_1947_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_st_ref_get(v___y_1951_);
lean_dec(v___x_1952_);
v___x_1953_ = lean_st_mk_ref(v_snd_1943_);
lean_inc(v_head_1937_);
v___x_1954_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1937_, v___x_1953_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = lean_st_ref_get(v___x_1953_);
lean_dec(v___x_1953_);
v___x_1957_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1958_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1937_);
lean_dec(v_head_1937_);
v___x_1959_ = lean_box(3);
v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1942_, v___x_1958_, v___x_1959_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1956_);
lean_ctor_set(v___x_1945_, 0, v___x_1960_);
v___x_1962_ = v___x_1945_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1956_);
v___x_1962_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
v_x_1929_ = v___x_1962_;
v_x_1930_ = v_tail_1938_;
goto _start;
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1965_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1937_);
lean_dec(v_head_1937_);
v___x_1966_ = lean_box(2);
v___x_1967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1942_, v___x_1965_, v___x_1966_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1956_);
lean_ctor_set(v___x_1945_, 0, v___x_1967_);
v___x_1969_ = v___x_1945_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1956_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
v_x_1929_ = v___x_1969_;
v_x_1930_ = v_tail_1938_;
goto _start;
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v___x_1953_);
lean_del_object(v___x_1945_);
lean_dec(v_fst_1942_);
lean_dec(v_tail_1938_);
lean_dec(v_head_1937_);
v_a_1972_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1954_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1954_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2001_, v_x_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_unsigned_to_nat(16u);
v___x_2011_ = lean_mk_array(v___x_2010_, v___x_2009_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_map_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2048_ = l_List_lengthTR___redArg(v_a_2016_);
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_unsigned_to_nat(4u);
v___x_2051_ = lean_nat_mul(v___x_2048_, v___x_2050_);
lean_dec(v___x_2048_);
v___x_2052_ = lean_unsigned_to_nat(3u);
v___x_2053_ = lean_nat_div(v___x_2051_, v___x_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = l_Nat_nextPowerOfTwo(v___x_2053_);
lean_dec(v___x_2053_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_mk_array(v___x_2054_, v___x_2055_);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2049_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
lean_inc(v_a_2016_);
v___x_2060_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2059_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v_fst_2062_; lean_object* v_discr_2063_; uint8_t v___x_2064_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v_fst_2062_ = lean_ctor_get(v_a_2061_, 0);
lean_inc(v_fst_2062_);
lean_dec(v_a_2061_);
v_discr_2063_ = lean_ctor_get(v_cs_2015_, 2);
v___x_2064_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2062_, v_discr_2063_);
if (v___x_2064_ == 0)
{
v_map_2023_ = v_fst_2062_;
v___y_2024_ = v_a_2016_;
v___y_2025_ = v_a_2017_;
v___y_2026_ = v_a_2018_;
v___y_2027_ = v_a_2019_;
v___y_2028_ = v_a_2020_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_box(2);
lean_inc(v_discr_2063_);
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2062_, v_discr_2063_, v___x_2065_);
v_map_2023_ = v___x_2066_;
v___y_2024_ = v_a_2016_;
v___y_2025_ = v_a_2017_;
v___y_2026_ = v_a_2018_;
v___y_2027_ = v_a_2019_;
v___y_2028_ = v_a_2020_;
goto v___jp_2022_;
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_cs_2015_);
v_a_2067_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2060_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2060_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
v___jp_2022_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_st_mk_ref(v_map_2023_);
v___x_2030_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_2015_, v___x_2029_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec_ref(v_cs_2015_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2038_; 
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_2030_, 0);
lean_dec(v_unused_2039_);
v___x_2032_ = v___x_2030_;
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v___x_2030_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = lean_st_ref_get(v___x_2029_);
lean_dec(v___x_2029_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2034_);
v___x_2036_ = v___x_2032_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v___x_2029_);
v_a_2040_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2030_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2030_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2083_, v_x_2084_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2092_, v_x_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
return v_res_2100_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_a_2101_, lean_object* v_x_2102_){
_start:
{
if (lean_obj_tag(v_x_2102_) == 0)
{
uint8_t v___x_2103_; 
v___x_2103_ = 0;
return v___x_2103_;
}
else
{
lean_object* v_key_2104_; lean_object* v_tail_2105_; uint8_t v___x_2106_; 
v_key_2104_ = lean_ctor_get(v_x_2102_, 0);
v_tail_2105_ = lean_ctor_get(v_x_2102_, 2);
v___x_2106_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2104_, v_a_2101_);
if (v___x_2106_ == 0)
{
v_x_2102_ = v_tail_2105_;
goto _start;
}
else
{
return v___x_2106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_a_2108_, lean_object* v_x_2109_){
_start:
{
uint8_t v_res_2110_; lean_object* v_r_2111_; 
v_res_2110_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2108_, v_x_2109_);
lean_dec(v_x_2109_);
lean_dec(v_a_2108_);
v_r_2111_ = lean_box(v_res_2110_);
return v_r_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object* v_a_2112_, lean_object* v_b_2113_, lean_object* v_x_2114_){
_start:
{
if (lean_obj_tag(v_x_2114_) == 0)
{
lean_dec(v_b_2113_);
lean_dec(v_a_2112_);
return v_x_2114_;
}
else
{
lean_object* v_key_2115_; lean_object* v_value_2116_; lean_object* v_tail_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2129_; 
v_key_2115_ = lean_ctor_get(v_x_2114_, 0);
v_value_2116_ = lean_ctor_get(v_x_2114_, 1);
v_tail_2117_ = lean_ctor_get(v_x_2114_, 2);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_x_2114_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2119_ = v_x_2114_;
v_isShared_2120_ = v_isSharedCheck_2129_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_tail_2117_);
lean_inc(v_value_2116_);
lean_inc(v_key_2115_);
lean_dec(v_x_2114_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2129_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
uint8_t v___x_2121_; 
v___x_2121_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2115_, v_a_2112_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2112_, v_b_2113_, v_tail_2117_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 2, v___x_2122_);
v___x_2124_ = v___x_2119_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_key_2115_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_value_2116_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
else
{
lean_object* v___x_2127_; 
lean_dec(v_value_2116_);
lean_dec(v_key_2115_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_b_2113_);
lean_ctor_set(v___x_2119_, 0, v_a_2112_);
v___x_2127_ = v___x_2119_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2112_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_b_2113_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_tail_2117_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 0)
{
return v_x_2130_;
}
else
{
lean_object* v_key_2132_; lean_object* v_value_2133_; lean_object* v_tail_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2157_; 
v_key_2132_ = lean_ctor_get(v_x_2131_, 0);
v_value_2133_ = lean_ctor_get(v_x_2131_, 1);
v_tail_2134_ = lean_ctor_get(v_x_2131_, 2);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_x_2131_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2136_ = v_x_2131_;
v_isShared_2137_ = v_isSharedCheck_2157_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_tail_2134_);
lean_inc(v_value_2133_);
lean_inc(v_key_2132_);
lean_dec(v_x_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2157_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; uint64_t v___x_2139_; uint64_t v___x_2140_; uint64_t v___x_2141_; uint64_t v_fold_2142_; uint64_t v___x_2143_; uint64_t v___x_2144_; uint64_t v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2138_ = lean_array_get_size(v_x_2130_);
v___x_2139_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_2132_);
v___x_2140_ = 32ULL;
v___x_2141_ = lean_uint64_shift_right(v___x_2139_, v___x_2140_);
v_fold_2142_ = lean_uint64_xor(v___x_2139_, v___x_2141_);
v___x_2143_ = 16ULL;
v___x_2144_ = lean_uint64_shift_right(v_fold_2142_, v___x_2143_);
v___x_2145_ = lean_uint64_xor(v_fold_2142_, v___x_2144_);
v___x_2146_ = lean_uint64_to_usize(v___x_2145_);
v___x_2147_ = lean_usize_of_nat(v___x_2138_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_sub(v___x_2147_, v___x_2148_);
v___x_2150_ = lean_usize_land(v___x_2146_, v___x_2149_);
v___x_2151_ = lean_array_uget_borrowed(v_x_2130_, v___x_2150_);
lean_inc(v___x_2151_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 2, v___x_2151_);
v___x_2153_ = v___x_2136_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_key_2132_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_value_2133_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_array_uset(v_x_2130_, v___x_2150_, v___x_2153_);
v_x_2130_ = v___x_2154_;
v_x_2131_ = v_tail_2134_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2158_, lean_object* v_source_2159_, lean_object* v_target_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_array_get_size(v_source_2159_);
v___x_2162_ = lean_nat_dec_lt(v_i_2158_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_dec_ref(v_source_2159_);
lean_dec(v_i_2158_);
return v_target_2160_;
}
else
{
lean_object* v_es_2163_; lean_object* v___x_2164_; lean_object* v_source_2165_; lean_object* v_target_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_es_2163_ = lean_array_fget(v_source_2159_, v_i_2158_);
v___x_2164_ = lean_box(0);
v_source_2165_ = lean_array_fset(v_source_2159_, v_i_2158_, v___x_2164_);
v_target_2166_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2160_, v_es_2163_);
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_add(v_i_2158_, v___x_2167_);
lean_dec(v_i_2158_);
v_i_2158_ = v___x_2168_;
v_source_2159_ = v_source_2165_;
v_target_2160_ = v_target_2166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object* v_data_2170_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_nbuckets_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2171_ = lean_array_get_size(v_data_2170_);
v___x_2172_ = lean_unsigned_to_nat(2u);
v_nbuckets_2173_ = lean_nat_mul(v___x_2171_, v___x_2172_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_mk_array(v_nbuckets_2173_, v___x_2175_);
v___x_2177_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2174_, v_data_2170_, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2178_, lean_object* v_a_2179_, lean_object* v_b_2180_){
_start:
{
lean_object* v_size_2181_; lean_object* v_buckets_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2225_; 
v_size_2181_ = lean_ctor_get(v_m_2178_, 0);
v_buckets_2182_ = lean_ctor_get(v_m_2178_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_m_2178_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2184_ = v_m_2178_;
v_isShared_2185_ = v_isSharedCheck_2225_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_buckets_2182_);
lean_inc(v_size_2181_);
lean_dec(v_m_2178_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2225_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; uint64_t v___x_2189_; uint64_t v_fold_2190_; uint64_t v___x_2191_; uint64_t v___x_2192_; uint64_t v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; size_t v___x_2198_; lean_object* v_bkt_2199_; uint8_t v___x_2200_; 
v___x_2186_ = lean_array_get_size(v_buckets_2182_);
v___x_2187_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2179_);
v___x_2188_ = 32ULL;
v___x_2189_ = lean_uint64_shift_right(v___x_2187_, v___x_2188_);
v_fold_2190_ = lean_uint64_xor(v___x_2187_, v___x_2189_);
v___x_2191_ = 16ULL;
v___x_2192_ = lean_uint64_shift_right(v_fold_2190_, v___x_2191_);
v___x_2193_ = lean_uint64_xor(v_fold_2190_, v___x_2192_);
v___x_2194_ = lean_uint64_to_usize(v___x_2193_);
v___x_2195_ = lean_usize_of_nat(v___x_2186_);
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_sub(v___x_2195_, v___x_2196_);
v___x_2198_ = lean_usize_land(v___x_2194_, v___x_2197_);
v_bkt_2199_ = lean_array_uget_borrowed(v_buckets_2182_, v___x_2198_);
v___x_2200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2179_, v_bkt_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v_size_x27_2202_; lean_object* v___x_2203_; lean_object* v_buckets_x27_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2201_ = lean_unsigned_to_nat(1u);
v_size_x27_2202_ = lean_nat_add(v_size_2181_, v___x_2201_);
lean_dec(v_size_2181_);
lean_inc(v_bkt_2199_);
v___x_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2179_);
lean_ctor_set(v___x_2203_, 1, v_b_2180_);
lean_ctor_set(v___x_2203_, 2, v_bkt_2199_);
v_buckets_x27_2204_ = lean_array_uset(v_buckets_2182_, v___x_2198_, v___x_2203_);
v___x_2205_ = lean_unsigned_to_nat(4u);
v___x_2206_ = lean_nat_mul(v_size_x27_2202_, v___x_2205_);
v___x_2207_ = lean_unsigned_to_nat(3u);
v___x_2208_ = lean_nat_div(v___x_2206_, v___x_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_array_get_size(v_buckets_x27_2204_);
v___x_2210_ = lean_nat_dec_le(v___x_2208_, v___x_2209_);
lean_dec(v___x_2208_);
if (v___x_2210_ == 0)
{
lean_object* v_val_2211_; lean_object* v___x_2213_; 
v_val_2211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2204_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v_val_2211_);
lean_ctor_set(v___x_2184_, 0, v_size_x27_2202_);
v___x_2213_ = v___x_2184_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_size_x27_2202_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_val_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
else
{
lean_object* v___x_2216_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v_buckets_x27_2204_);
lean_ctor_set(v___x_2184_, 0, v_size_x27_2202_);
v___x_2216_ = v___x_2184_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_size_x27_2202_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_buckets_x27_2204_);
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
lean_object* v___x_2218_; lean_object* v_buckets_x27_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
lean_inc(v_bkt_2199_);
v___x_2218_ = lean_box(0);
v_buckets_x27_2219_ = lean_array_uset(v_buckets_2182_, v___x_2198_, v___x_2218_);
v___x_2220_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2179_, v_b_2180_, v_bkt_2199_);
v___x_2221_ = lean_array_uset(v_buckets_x27_2219_, v___x_2198_, v___x_2220_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v___x_2221_);
v___x_2223_ = v___x_2184_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_size_2181_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2226_, size_t v_i_2227_, size_t v_stop_2228_, lean_object* v_b_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_eq(v_i_2227_, v_stop_2228_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_sub(v_i_2227_, v___x_2232_);
v___x_2234_ = lean_array_uget_borrowed(v_as_2226_, v___x_2233_);
v___x_2235_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2234_);
v___x_2236_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2229_, v___x_2235_, v___x_2231_);
v_i_2227_ = v___x_2233_;
v_b_2229_ = v___x_2236_;
goto _start;
}
else
{
return v_b_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2238_, lean_object* v_i_2239_, lean_object* v_stop_2240_, lean_object* v_b_2241_){
_start:
{
size_t v_i_boxed_2242_; size_t v_stop_boxed_2243_; lean_object* v_res_2244_; 
v_i_boxed_2242_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_stop_boxed_2243_ = lean_unbox_usize(v_stop_2240_);
lean_dec(v_stop_2240_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2238_, v_i_boxed_2242_, v_stop_boxed_2243_, v_b_2241_);
lean_dec_ref(v_as_2238_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2245_){
_start:
{
lean_object* v_alts_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_map_2261_; uint8_t v___x_2262_; 
v_alts_2246_ = lean_ctor_get(v_cs_2245_, 3);
v___x_2247_ = lean_array_get_size(v_alts_2246_);
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v___x_2247_, v___x_2248_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = lean_unsigned_to_nat(4u);
v___x_2252_ = lean_nat_mul(v___x_2249_, v___x_2251_);
lean_dec(v___x_2249_);
v___x_2253_ = lean_unsigned_to_nat(3u);
v___x_2254_ = lean_nat_div(v___x_2252_, v___x_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = l_Nat_nextPowerOfTwo(v___x_2254_);
lean_dec(v___x_2254_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_mk_array(v___x_2255_, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2250_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_box(2);
v___x_2260_ = lean_box(0);
v_map_2261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2258_, v___x_2259_, v___x_2260_);
v___x_2262_ = lean_nat_dec_lt(v___x_2250_, v___x_2247_);
if (v___x_2262_ == 0)
{
return v_map_2261_;
}
else
{
size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_usize_of_nat(v___x_2247_);
v___x_2264_ = ((size_t)0ULL);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2246_, v___x_2263_, v___x_2264_, v_map_2261_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2266_);
lean_dec_ref(v_cs_2266_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2268_, lean_object* v_m_2269_, lean_object* v_a_2270_, lean_object* v_b_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2269_, v_a_2270_, v_b_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2273_, lean_object* v_a_2274_, lean_object* v_x_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2274_, v_x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2277_, lean_object* v_a_2278_, lean_object* v_x_2279_){
_start:
{
uint8_t v_res_2280_; lean_object* v_r_2281_; 
v_res_2280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2277_, v_a_2278_, v_x_2279_);
lean_dec(v_x_2279_);
lean_dec(v_a_2278_);
v_r_2281_ = lean_box(v_res_2280_);
return v_r_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2282_, lean_object* v_data_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2285_, lean_object* v_a_2286_, lean_object* v_b_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2286_, v_b_2287_, v_x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2290_, lean_object* v_i_2291_, lean_object* v_source_2292_, lean_object* v_target_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2291_, v_source_2292_, v_target_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2296_, v_x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; lean_object* v_decision_2303_; uint8_t v___x_2304_; 
v___x_2302_ = lean_st_ref_get(v_a_2300_);
v_decision_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc_ref(v_decision_2303_);
lean_dec(v___x_2302_);
v___x_2304_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2303_, v_fvar_2299_);
lean_dec_ref(v_decision_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_fvar_2299_);
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
else
{
lean_object* v___x_2307_; lean_object* v_decision_2308_; lean_object* v_newArms_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2321_; 
v___x_2307_ = lean_st_ref_take(v_a_2300_);
v_decision_2308_ = lean_ctor_get(v___x_2307_, 0);
v_newArms_2309_ = lean_ctor_get(v___x_2307_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2311_ = v___x_2307_;
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_newArms_2309_);
lean_inc(v_decision_2308_);
lean_dec(v___x_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = lean_box(2);
v___x_2314_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2308_, v_fvar_2299_, v___x_2313_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2314_);
v___x_2316_ = v___x_2311_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_newArms_2309_);
v___x_2316_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_st_ref_set(v_a_2300_, v___x_2316_);
v___x_2318_ = lean_box(0);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2322_, v_a_2323_);
lean_dec(v_a_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2326_, v_a_2327_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec(v_a_2336_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_toApplicative_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2417_; 
v___x_2352_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2353_ = l_StateRefT_x27_instMonad___redArg(v___x_2352_);
v_toApplicative_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v___x_2353_, 1);
lean_dec(v_unused_2418_);
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2417_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_toApplicative_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2417_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_toFunctor_2358_; lean_object* v_toSeq_2359_; lean_object* v_toSeqLeft_2360_; lean_object* v_toSeqRight_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2415_; 
v_toFunctor_2358_ = lean_ctor_get(v_toApplicative_2354_, 0);
v_toSeq_2359_ = lean_ctor_get(v_toApplicative_2354_, 2);
v_toSeqLeft_2360_ = lean_ctor_get(v_toApplicative_2354_, 3);
v_toSeqRight_2361_ = lean_ctor_get(v_toApplicative_2354_, 4);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_toApplicative_2354_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v_toApplicative_2354_, 1);
lean_dec(v_unused_2416_);
v___x_2363_ = v_toApplicative_2354_;
v_isShared_2364_ = v_isSharedCheck_2415_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_toSeqRight_2361_);
lean_inc(v_toSeqLeft_2360_);
lean_inc(v_toSeq_2359_);
lean_inc(v_toFunctor_2358_);
lean_dec(v_toApplicative_2354_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2415_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v___f_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; lean_object* v___x_2374_; 
v___f_2365_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2366_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2358_);
v___f_2367_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2367_, 0, v_toFunctor_2358_);
v___f_2368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2368_, 0, v_toFunctor_2358_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___f_2367_);
lean_ctor_set(v___x_2369_, 1, v___f_2368_);
v___f_2370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2370_, 0, v_toSeqRight_2361_);
v___f_2371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2371_, 0, v_toSeqLeft_2360_);
v___f_2372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2372_, 0, v_toSeq_2359_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 4, v___f_2370_);
lean_ctor_set(v___x_2363_, 3, v___f_2371_);
lean_ctor_set(v___x_2363_, 2, v___f_2372_);
lean_ctor_set(v___x_2363_, 1, v___f_2365_);
lean_ctor_set(v___x_2363_, 0, v___x_2369_);
v___x_2374_ = v___x_2363_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___f_2365_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___f_2372_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v___f_2371_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v___f_2370_);
v___x_2374_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 1, v___f_2366_);
lean_ctor_set(v___x_2356_, 0, v___x_2374_);
v___x_2376_ = v___x_2356_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___f_2366_);
v___x_2376_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v_toApplicative_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2411_; 
v___x_2377_ = l_StateRefT_x27_instMonad___redArg(v___x_2376_);
v_toApplicative_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2377_, 1);
lean_dec(v_unused_2412_);
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2411_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_toApplicative_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2411_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_toFunctor_2382_; lean_object* v_toSeq_2383_; lean_object* v_toSeqLeft_2384_; lean_object* v_toSeqRight_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2409_; 
v_toFunctor_2382_ = lean_ctor_get(v_toApplicative_2378_, 0);
v_toSeq_2383_ = lean_ctor_get(v_toApplicative_2378_, 2);
v_toSeqLeft_2384_ = lean_ctor_get(v_toApplicative_2378_, 3);
v_toSeqRight_2385_ = lean_ctor_get(v_toApplicative_2378_, 4);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_toApplicative_2378_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_toApplicative_2378_, 1);
lean_dec(v_unused_2410_);
v___x_2387_ = v_toApplicative_2378_;
v_isShared_2388_ = v_isSharedCheck_2409_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_toSeqRight_2385_);
lean_inc(v_toSeqLeft_2384_);
lean_inc(v_toSeq_2383_);
lean_inc(v_toFunctor_2382_);
lean_dec(v_toApplicative_2378_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2409_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___f_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___f_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; lean_object* v___f_2395_; lean_object* v___f_2396_; lean_object* v___x_2398_; 
v___f_2389_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2390_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2382_);
v___f_2391_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2391_, 0, v_toFunctor_2382_);
v___f_2392_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2392_, 0, v_toFunctor_2382_);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___f_2391_);
lean_ctor_set(v___x_2393_, 1, v___f_2392_);
v___f_2394_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2394_, 0, v_toSeqRight_2385_);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2395_, 0, v_toSeqLeft_2384_);
v___f_2396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2396_, 0, v_toSeq_2383_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 4, v___f_2394_);
lean_ctor_set(v___x_2387_, 3, v___f_2395_);
lean_ctor_set(v___x_2387_, 2, v___f_2396_);
lean_ctor_set(v___x_2387_, 1, v___f_2389_);
lean_ctor_set(v___x_2387_, 0, v___x_2393_);
v___x_2398_ = v___x_2387_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___f_2389_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v___f_2396_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v___f_2395_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v___f_2394_);
v___x_2398_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v___f_2390_);
lean_ctor_set(v___x_2380_, 0, v___x_2398_);
v___x_2400_ = v___x_2380_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___f_2390_);
v___x_2400_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_12636__overap_2405_; lean_object* v___x_2406_; 
v___x_2401_ = l_ReaderT_instMonad___redArg(v___x_2400_);
v___x_2402_ = l_StateRefT_x27_instMonad___redArg(v___x_2401_);
v___x_2403_ = lean_box(0);
v___x_2404_ = l_instInhabitedOfMonad___redArg(v___x_2402_, v___x_2403_);
v___x_12636__overap_2405_ = lean_panic_fn_borrowed(v___x_2404_, v_msg_2344_);
lean_dec(v___x_2404_);
lean_inc(v___y_2350_);
lean_inc_ref(v___y_2349_);
lean_inc(v___y_2348_);
lean_inc_ref(v___y_2347_);
lean_inc(v___y_2346_);
lean_inc(v___y_2345_);
v___x_2406_ = lean_apply_7(v___x_12636__overap_2405_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, lean_box(0));
return v___x_2406_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec(v___y_2420_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2428_, lean_object* v_e_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_ty_2438_; lean_object* v_body_2439_; uint8_t v___x_2442_; 
v___x_2442_ = l_Lean_Expr_hasFVar(v_e_2429_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec_ref(v_e_2429_);
lean_dec_ref(v_f_2428_);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
else
{
switch(lean_obj_tag(v_e_2429_))
{
case 1:
{
lean_object* v_fvarId_2445_; lean_object* v___x_2446_; 
v_fvarId_2445_ = lean_ctor_get(v_e_2429_, 0);
lean_inc(v_fvarId_2445_);
lean_dec_ref_known(v_e_2429_, 1);
lean_inc(v___y_2435_);
lean_inc_ref(v___y_2434_);
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2432_);
lean_inc(v___y_2431_);
lean_inc(v___y_2430_);
v___x_2446_ = lean_apply_8(v_f_2428_, v_fvarId_2445_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, lean_box(0));
return v___x_2446_;
}
case 2:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref_known(v_e_2429_, 1);
lean_dec_ref(v_f_2428_);
v___x_2447_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2448_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2447_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2448_;
}
case 5:
{
lean_object* v_fn_2449_; lean_object* v_arg_2450_; lean_object* v___x_2451_; 
v_fn_2449_ = lean_ctor_get(v_e_2429_, 0);
lean_inc_ref(v_fn_2449_);
v_arg_2450_ = lean_ctor_get(v_e_2429_, 1);
lean_inc_ref(v_arg_2450_);
lean_dec_ref_known(v_e_2429_, 2);
lean_inc_ref(v_f_2428_);
v___x_2451_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2428_, v_fn_2449_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec_ref_known(v___x_2451_, 1);
v_e_2429_ = v_arg_2450_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_f_2428_);
return v___x_2451_;
}
}
case 6:
{
lean_object* v_binderType_2453_; lean_object* v_body_2454_; 
v_binderType_2453_ = lean_ctor_get(v_e_2429_, 1);
lean_inc_ref(v_binderType_2453_);
v_body_2454_ = lean_ctor_get(v_e_2429_, 2);
lean_inc_ref(v_body_2454_);
lean_dec_ref_known(v_e_2429_, 3);
v_ty_2438_ = v_binderType_2453_;
v_body_2439_ = v_body_2454_;
goto v___jp_2437_;
}
case 7:
{
lean_object* v_binderType_2455_; lean_object* v_body_2456_; 
v_binderType_2455_ = lean_ctor_get(v_e_2429_, 1);
lean_inc_ref(v_binderType_2455_);
v_body_2456_ = lean_ctor_get(v_e_2429_, 2);
lean_inc_ref(v_body_2456_);
lean_dec_ref_known(v_e_2429_, 3);
v_ty_2438_ = v_binderType_2455_;
v_body_2439_ = v_body_2456_;
goto v___jp_2437_;
}
case 8:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec_ref_known(v_e_2429_, 4);
lean_dec_ref(v_f_2428_);
v___x_2457_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2458_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2457_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2458_;
}
case 11:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec_ref_known(v_e_2429_, 3);
lean_dec_ref(v_f_2428_);
v___x_2459_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2460_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2459_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2460_;
}
default: 
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref(v_e_2429_);
lean_dec_ref(v_f_2428_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
}
}
v___jp_2437_:
{
lean_object* v___x_2440_; 
lean_inc_ref(v_f_2428_);
v___x_2440_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2428_, v_ty_2438_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_dec_ref_known(v___x_2440_, 1);
v_e_2429_ = v_body_2439_;
goto _start;
}
else
{
lean_dec_ref(v_body_2439_);
lean_dec_ref(v_f_2428_);
return v___x_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2463_, lean_object* v_e_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2463_, v_e_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec(v___y_2465_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2473_, lean_object* v_arg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
switch(lean_obj_tag(v_arg_2474_))
{
case 0:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref(v_f_2473_);
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
case 1:
{
lean_object* v_fvarId_2484_; lean_object* v___x_2485_; 
v_fvarId_2484_ = lean_ctor_get(v_arg_2474_, 0);
lean_inc(v_fvarId_2484_);
lean_dec_ref_known(v_arg_2474_, 1);
lean_inc(v___y_2480_);
lean_inc_ref(v___y_2479_);
lean_inc(v___y_2478_);
lean_inc_ref(v___y_2477_);
lean_inc(v___y_2476_);
lean_inc(v___y_2475_);
v___x_2485_ = lean_apply_8(v_f_2473_, v_fvarId_2484_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, lean_box(0));
return v___x_2485_;
}
default: 
{
lean_object* v_expr_2486_; lean_object* v___x_2487_; 
v_expr_2486_ = lean_ctor_get(v_arg_2474_, 0);
lean_inc_ref(v_expr_2486_);
lean_dec_ref_known(v_arg_2474_, 1);
v___x_2487_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2473_, v_expr_2486_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2488_, lean_object* v_arg_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2488_, v_arg_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2498_, lean_object* v_param_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_type_2507_; lean_object* v___x_2508_; 
v_type_2507_ = lean_ctor_get(v_param_2499_, 2);
lean_inc_ref(v_type_2507_);
lean_dec_ref(v_param_2499_);
v___x_2508_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2498_, v_type_2507_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2509_, lean_object* v_param_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2509_, v_param_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec(v___y_2511_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2519_, lean_object* v_f_2520_, lean_object* v_as_2521_, size_t v_i_2522_, size_t v_stop_2523_, lean_object* v_b_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_usize_dec_eq(v_i_2522_, v_stop_2523_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_array_uget_borrowed(v_as_2521_, v_i_2522_);
lean_inc(v___x_2533_);
lean_inc_ref(v_f_2520_);
v___x_2534_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2520_, v___x_2533_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; size_t v___x_2536_; size_t v___x_2537_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_add(v_i_2522_, v___x_2536_);
v_i_2522_ = v___x_2537_;
v_b_2524_ = v_a_2535_;
goto _start;
}
else
{
lean_dec_ref(v_f_2520_);
return v___x_2534_;
}
}
else
{
lean_object* v___x_2539_; 
lean_dec_ref(v_f_2520_);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_b_2524_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2540_, lean_object* v_f_2541_, lean_object* v_as_2542_, lean_object* v_i_2543_, lean_object* v_stop_2544_, lean_object* v_b_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v_pu_boxed_2553_; size_t v_i_boxed_2554_; size_t v_stop_boxed_2555_; lean_object* v_res_2556_; 
v_pu_boxed_2553_ = lean_unbox(v_pu_2540_);
v_i_boxed_2554_ = lean_unbox_usize(v_i_2543_);
lean_dec(v_i_2543_);
v_stop_boxed_2555_ = lean_unbox_usize(v_stop_2544_);
lean_dec(v_stop_2544_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2553_, v_f_2541_, v_as_2542_, v_i_boxed_2554_, v_stop_boxed_2555_, v_b_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v_as_2542_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2557_, lean_object* v_f_2558_, lean_object* v_as_2559_, size_t v_i_2560_, size_t v_stop_2561_, lean_object* v_b_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_usize_dec_eq(v_i_2560_, v_stop_2561_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_array_uget_borrowed(v_as_2559_, v_i_2560_);
lean_inc(v___x_2571_);
lean_inc_ref(v_f_2558_);
v___x_2572_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2558_, v___x_2571_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; size_t v___x_2574_; size_t v___x_2575_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v___x_2574_ = ((size_t)1ULL);
v___x_2575_ = lean_usize_add(v_i_2560_, v___x_2574_);
v_i_2560_ = v___x_2575_;
v_b_2562_ = v_a_2573_;
goto _start;
}
else
{
lean_dec_ref(v_f_2558_);
return v___x_2572_;
}
}
else
{
lean_object* v___x_2577_; 
lean_dec_ref(v_f_2558_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_b_2562_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2578_, lean_object* v_f_2579_, lean_object* v_as_2580_, lean_object* v_i_2581_, lean_object* v_stop_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v_pu_boxed_2591_; size_t v_i_boxed_2592_; size_t v_stop_boxed_2593_; lean_object* v_res_2594_; 
v_pu_boxed_2591_ = lean_unbox(v_pu_2578_);
v_i_boxed_2592_ = lean_unbox_usize(v_i_2581_);
lean_dec(v_i_2581_);
v_stop_boxed_2593_ = lean_unbox_usize(v_stop_2582_);
lean_dec(v_stop_2582_);
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2591_, v_f_2579_, v_as_2580_, v_i_boxed_2592_, v_stop_boxed_2593_, v_b_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v_as_2580_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2595_, lean_object* v_f_2596_, lean_object* v_e_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_args_2606_; 
switch(lean_obj_tag(v_e_2597_))
{
case 2:
{
lean_object* v_struct_2620_; lean_object* v___x_2621_; 
v_struct_2620_ = lean_ctor_get(v_e_2597_, 2);
lean_inc(v_struct_2620_);
lean_dec_ref_known(v_e_2597_, 3);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2621_ = lean_apply_8(v_f_2596_, v_struct_2620_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2621_;
}
case 3:
{
lean_object* v_args_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_args_2622_ = lean_ctor_get(v_e_2597_, 2);
lean_inc_ref(v_args_2622_);
lean_dec_ref_known(v_e_2597_, 3);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_array_get_size(v_args_2622_);
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_nat_dec_lt(v___x_2623_, v___x_2624_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v_args_2622_);
lean_dec_ref(v_f_2596_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
return v___x_2627_;
}
else
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_nat_dec_le(v___x_2624_, v___x_2624_);
if (v___x_2628_ == 0)
{
if (v___x_2626_ == 0)
{
lean_object* v___x_2629_; 
lean_dec_ref(v_args_2622_);
lean_dec_ref(v_f_2596_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2625_);
return v___x_2629_;
}
else
{
size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = lean_usize_of_nat(v___x_2624_);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2622_, v___x_2630_, v___x_2631_, v___x_2625_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2622_);
return v___x_2632_;
}
}
else
{
size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = lean_usize_of_nat(v___x_2624_);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2622_, v___x_2633_, v___x_2634_, v___x_2625_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2622_);
return v___x_2635_;
}
}
}
case 4:
{
lean_object* v_fvarId_2636_; lean_object* v_args_2637_; lean_object* v___x_2638_; 
v_fvarId_2636_ = lean_ctor_get(v_e_2597_, 0);
lean_inc(v_fvarId_2636_);
v_args_2637_ = lean_ctor_get(v_e_2597_, 1);
lean_inc_ref(v_args_2637_);
lean_dec_ref_known(v_e_2597_, 2);
lean_inc_ref(v_f_2596_);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2638_ = lean_apply_8(v_f_2596_, v_fvarId_2636_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2659_; 
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2659_ == 0)
{
lean_object* v_unused_2660_; 
v_unused_2660_ = lean_ctor_get(v___x_2638_, 0);
lean_dec(v_unused_2660_);
v___x_2640_ = v___x_2638_;
v_isShared_2641_ = v_isSharedCheck_2659_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v___x_2638_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2659_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_array_get_size(v_args_2637_);
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_nat_dec_lt(v___x_2642_, v___x_2643_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2647_; 
lean_dec_ref(v_args_2637_);
lean_dec_ref(v_f_2596_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2644_);
v___x_2647_ = v___x_2640_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2644_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_nat_dec_le(v___x_2643_, v___x_2643_);
if (v___x_2649_ == 0)
{
if (v___x_2645_ == 0)
{
lean_object* v___x_2651_; 
lean_dec_ref(v_args_2637_);
lean_dec_ref(v_f_2596_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2644_);
v___x_2651_ = v___x_2640_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2644_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
lean_del_object(v___x_2640_);
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2643_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2637_, v___x_2653_, v___x_2654_, v___x_2644_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2637_);
return v___x_2655_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2640_);
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2643_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2637_, v___x_2656_, v___x_2657_, v___x_2644_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2637_);
return v___x_2658_;
}
}
}
}
else
{
lean_dec_ref(v_args_2637_);
lean_dec_ref(v_f_2596_);
return v___x_2638_;
}
}
case 5:
{
lean_object* v_args_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v_args_2661_ = lean_ctor_get(v_e_2597_, 1);
lean_inc_ref(v_args_2661_);
lean_dec_ref_known(v_e_2597_, 2);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v_args_2661_);
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref(v_args_2661_);
lean_dec_ref(v_f_2596_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
return v___x_2666_;
}
else
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_nat_dec_le(v___x_2663_, v___x_2663_);
if (v___x_2667_ == 0)
{
if (v___x_2665_ == 0)
{
lean_object* v___x_2668_; 
lean_dec_ref(v_args_2661_);
lean_dec_ref(v_f_2596_);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2664_);
return v___x_2668_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2663_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2661_, v___x_2669_, v___x_2670_, v___x_2664_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2661_);
return v___x_2671_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2663_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2661_, v___x_2672_, v___x_2673_, v___x_2664_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2661_);
return v___x_2674_;
}
}
}
case 6:
{
lean_object* v_var_2675_; lean_object* v___x_2676_; 
v_var_2675_ = lean_ctor_get(v_e_2597_, 1);
lean_inc(v_var_2675_);
lean_dec_ref_known(v_e_2597_, 2);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2676_ = lean_apply_8(v_f_2596_, v_var_2675_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2676_;
}
case 7:
{
lean_object* v_var_2677_; lean_object* v___x_2678_; 
v_var_2677_ = lean_ctor_get(v_e_2597_, 1);
lean_inc(v_var_2677_);
lean_dec_ref_known(v_e_2597_, 2);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2678_ = lean_apply_8(v_f_2596_, v_var_2677_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2678_;
}
case 8:
{
lean_object* v_var_2679_; lean_object* v___x_2680_; 
v_var_2679_ = lean_ctor_get(v_e_2597_, 2);
lean_inc(v_var_2679_);
lean_dec_ref_known(v_e_2597_, 3);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2680_ = lean_apply_8(v_f_2596_, v_var_2679_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2680_;
}
case 9:
{
lean_object* v_args_2681_; 
v_args_2681_ = lean_ctor_get(v_e_2597_, 1);
lean_inc_ref(v_args_2681_);
lean_dec_ref_known(v_e_2597_, 2);
v_args_2606_ = v_args_2681_;
goto v___jp_2605_;
}
case 10:
{
lean_object* v_args_2682_; 
v_args_2682_ = lean_ctor_get(v_e_2597_, 1);
lean_inc_ref(v_args_2682_);
lean_dec_ref_known(v_e_2597_, 2);
v_args_2606_ = v_args_2682_;
goto v___jp_2605_;
}
case 11:
{
lean_object* v_var_2683_; lean_object* v___x_2684_; 
v_var_2683_ = lean_ctor_get(v_e_2597_, 1);
lean_inc(v_var_2683_);
lean_dec_ref_known(v_e_2597_, 2);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2684_ = lean_apply_8(v_f_2596_, v_var_2683_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2684_;
}
case 12:
{
lean_object* v_var_2685_; lean_object* v_args_2686_; lean_object* v___x_2687_; 
v_var_2685_ = lean_ctor_get(v_e_2597_, 0);
lean_inc(v_var_2685_);
v_args_2686_ = lean_ctor_get(v_e_2597_, 2);
lean_inc_ref(v_args_2686_);
lean_dec_ref_known(v_e_2597_, 3);
lean_inc_ref(v_f_2596_);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2687_ = lean_apply_8(v_f_2596_, v_var_2685_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2708_; 
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___x_2687_, 0);
lean_dec(v_unused_2709_);
v___x_2689_ = v___x_2687_;
v_isShared_2690_ = v_isSharedCheck_2708_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v___x_2687_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2708_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2691_ = lean_unsigned_to_nat(0u);
v___x_2692_ = lean_array_get_size(v_args_2686_);
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_nat_dec_lt(v___x_2691_, v___x_2692_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2696_; 
lean_dec_ref(v_args_2686_);
lean_dec_ref(v_f_2596_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2693_);
v___x_2696_ = v___x_2689_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2693_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
else
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_nat_dec_le(v___x_2692_, v___x_2692_);
if (v___x_2698_ == 0)
{
if (v___x_2694_ == 0)
{
lean_object* v___x_2700_; 
lean_dec_ref(v_args_2686_);
lean_dec_ref(v_f_2596_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2693_);
v___x_2700_ = v___x_2689_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2693_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
else
{
size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; 
lean_del_object(v___x_2689_);
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = lean_usize_of_nat(v___x_2692_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2686_, v___x_2702_, v___x_2703_, v___x_2693_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2686_);
return v___x_2704_;
}
}
else
{
size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
lean_del_object(v___x_2689_);
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = lean_usize_of_nat(v___x_2692_);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2686_, v___x_2705_, v___x_2706_, v___x_2693_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2686_);
return v___x_2707_;
}
}
}
}
else
{
lean_dec_ref(v_args_2686_);
lean_dec_ref(v_f_2596_);
return v___x_2687_;
}
}
case 13:
{
lean_object* v_fvarId_2710_; lean_object* v___x_2711_; 
v_fvarId_2710_ = lean_ctor_get(v_e_2597_, 1);
lean_inc(v_fvarId_2710_);
lean_dec_ref_known(v_e_2597_, 2);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2711_ = lean_apply_8(v_f_2596_, v_fvarId_2710_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2711_;
}
case 14:
{
lean_object* v_fvarId_2712_; lean_object* v___x_2713_; 
v_fvarId_2712_ = lean_ctor_get(v_e_2597_, 0);
lean_inc(v_fvarId_2712_);
lean_dec_ref_known(v_e_2597_, 1);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2713_ = lean_apply_8(v_f_2596_, v_fvarId_2712_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2713_;
}
case 15:
{
lean_object* v_fvarId_2714_; lean_object* v___x_2715_; 
v_fvarId_2714_ = lean_ctor_get(v_e_2597_, 0);
lean_inc(v_fvarId_2714_);
lean_dec_ref_known(v_e_2597_, 1);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc(v___y_2598_);
v___x_2715_ = lean_apply_8(v_f_2596_, v_fvarId_2714_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2715_;
}
default: 
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec(v_e_2597_);
lean_dec_ref(v_f_2596_);
v___x_2716_ = lean_box(0);
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
}
v___jp_2605_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2607_ = lean_unsigned_to_nat(0u);
v___x_2608_ = lean_array_get_size(v_args_2606_);
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_nat_dec_lt(v___x_2607_, v___x_2608_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_dec_ref(v_args_2606_);
lean_dec_ref(v_f_2596_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
return v___x_2611_;
}
else
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_nat_dec_le(v___x_2608_, v___x_2608_);
if (v___x_2612_ == 0)
{
if (v___x_2610_ == 0)
{
lean_object* v___x_2613_; 
lean_dec_ref(v_args_2606_);
lean_dec_ref(v_f_2596_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2609_);
return v___x_2613_;
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2608_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2606_, v___x_2614_, v___x_2615_, v___x_2609_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2606_);
return v___x_2616_;
}
}
else
{
size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = ((size_t)0ULL);
v___x_2618_ = lean_usize_of_nat(v___x_2608_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2595_, v_f_2596_, v_args_2606_, v___x_2617_, v___x_2618_, v___x_2609_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec_ref(v_args_2606_);
return v___x_2619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2718_, lean_object* v_f_2719_, lean_object* v_e_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v_pu_boxed_2728_; lean_object* v_res_2729_; 
v_pu_boxed_2728_ = lean_unbox(v_pu_2718_);
v_res_2729_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2728_, v_f_2719_, v_e_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2730_, lean_object* v_f_2731_, lean_object* v_decl_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_type_2740_; lean_object* v_value_2741_; lean_object* v___x_2742_; 
v_type_2740_ = lean_ctor_get(v_decl_2732_, 2);
lean_inc_ref(v_type_2740_);
v_value_2741_ = lean_ctor_get(v_decl_2732_, 3);
lean_inc(v_value_2741_);
lean_dec_ref(v_decl_2732_);
lean_inc_ref(v_f_2731_);
v___x_2742_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2731_, v_type_2740_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v___x_2743_; 
lean_dec_ref_known(v___x_2742_, 1);
v___x_2743_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2730_, v_f_2731_, v_value_2741_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2743_;
}
else
{
lean_dec(v_value_2741_);
lean_dec_ref(v_f_2731_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2744_, lean_object* v_f_2745_, lean_object* v_decl_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v_pu_boxed_2754_; lean_object* v_res_2755_; 
v_pu_boxed_2754_ = lean_unbox(v_pu_2744_);
v_res_2755_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2754_, v_f_2745_, v_decl_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2747_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2756_, lean_object* v_f_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
switch(lean_obj_tag(v_alt_2756_))
{
case 0:
{
lean_object* v_code_2765_; lean_object* v___x_2766_; 
v_code_2765_ = lean_ctor_get(v_alt_2756_, 2);
lean_inc_ref(v_code_2765_);
lean_dec_ref_known(v_alt_2756_, 3);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc(v___y_2758_);
v___x_2766_ = lean_apply_8(v_f_2757_, v_code_2765_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, lean_box(0));
return v___x_2766_;
}
case 1:
{
lean_object* v_code_2767_; lean_object* v___x_2768_; 
v_code_2767_ = lean_ctor_get(v_alt_2756_, 1);
lean_inc_ref(v_code_2767_);
lean_dec_ref_known(v_alt_2756_, 2);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc(v___y_2758_);
v___x_2768_ = lean_apply_8(v_f_2757_, v_code_2767_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, lean_box(0));
return v___x_2768_;
}
default: 
{
lean_object* v_code_2769_; lean_object* v___x_2770_; 
v_code_2769_ = lean_ctor_get(v_alt_2756_, 0);
lean_inc_ref(v_code_2769_);
lean_dec_ref_known(v_alt_2756_, 1);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc(v___y_2758_);
v___x_2770_ = lean_apply_8(v_f_2757_, v_code_2769_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, lean_box(0));
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2771_, lean_object* v_f_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2771_, v_f_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec(v___y_2773_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2781_, lean_object* v_f_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
uint8_t v_pu_boxed_2791_; lean_object* v_res_2792_; 
v_pu_boxed_2791_ = lean_unbox(v_pu_2781_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2791_, v_f_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec(v___y_2784_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2793_, lean_object* v_f_2794_, lean_object* v_as_2795_, size_t v_i_2796_, size_t v_stop_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = lean_usize_dec_eq(v_i_2796_, v_stop_2797_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2807_ = lean_box(v_pu_2793_);
lean_inc_ref(v_f_2794_);
v___f_2808_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2808_, 0, v___x_2807_);
lean_closure_set(v___f_2808_, 1, v_f_2794_);
v___x_2809_ = lean_array_uget_borrowed(v_as_2795_, v_i_2796_);
lean_inc(v___x_2809_);
v___x_2810_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2809_, v___f_2808_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; size_t v___x_2812_; size_t v___x_2813_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = ((size_t)1ULL);
v___x_2813_ = lean_usize_add(v_i_2796_, v___x_2812_);
v_i_2796_ = v___x_2813_;
v_b_2798_ = v_a_2811_;
goto _start;
}
else
{
lean_dec_ref(v_f_2794_);
return v___x_2810_;
}
}
else
{
lean_object* v___x_2815_; 
lean_dec_ref(v_f_2794_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v_b_2798_);
return v___x_2815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2816_, lean_object* v_f_2817_, lean_object* v_c_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
switch(lean_obj_tag(v_c_2818_))
{
case 0:
{
lean_object* v_decl_2826_; lean_object* v_k_2827_; lean_object* v___x_2828_; 
v_decl_2826_ = lean_ctor_get(v_c_2818_, 0);
lean_inc_ref(v_decl_2826_);
v_k_2827_ = lean_ctor_get(v_c_2818_, 1);
lean_inc_ref(v_k_2827_);
lean_dec_ref_known(v_c_2818_, 2);
lean_inc_ref(v_f_2817_);
v___x_2828_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2816_, v_f_2817_, v_decl_2826_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_dec_ref_known(v___x_2828_, 1);
v_c_2818_ = v_k_2827_;
goto _start;
}
else
{
lean_dec_ref(v_k_2827_);
lean_dec_ref(v_f_2817_);
return v___x_2828_;
}
}
case 3:
{
lean_object* v_fvarId_2830_; lean_object* v_args_2831_; lean_object* v___x_2832_; 
v_fvarId_2830_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2830_);
v_args_2831_ = lean_ctor_get(v_c_2818_, 1);
lean_inc_ref(v_args_2831_);
lean_dec_ref_known(v_c_2818_, 2);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2832_ = lean_apply_8(v_f_2817_, v_fvarId_2830_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2853_; 
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; 
v_unused_2854_ = lean_ctor_get(v___x_2832_, 0);
lean_dec(v_unused_2854_);
v___x_2834_ = v___x_2832_;
v_isShared_2835_ = v_isSharedCheck_2853_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2832_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2853_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = lean_array_get_size(v_args_2831_);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_nat_dec_lt(v___x_2836_, v___x_2837_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref(v_args_2831_);
lean_dec_ref(v_f_2817_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2838_);
v___x_2841_ = v___x_2834_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
else
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_nat_dec_le(v___x_2837_, v___x_2837_);
if (v___x_2843_ == 0)
{
if (v___x_2839_ == 0)
{
lean_object* v___x_2845_; 
lean_dec_ref(v_args_2831_);
lean_dec_ref(v_f_2817_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2838_);
v___x_2845_ = v___x_2834_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2838_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
else
{
size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; 
lean_del_object(v___x_2834_);
v___x_2847_ = ((size_t)0ULL);
v___x_2848_ = lean_usize_of_nat(v___x_2837_);
v___x_2849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2816_, v_f_2817_, v_args_2831_, v___x_2847_, v___x_2848_, v___x_2838_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_args_2831_);
return v___x_2849_;
}
}
else
{
size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
lean_del_object(v___x_2834_);
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = lean_usize_of_nat(v___x_2837_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2816_, v_f_2817_, v_args_2831_, v___x_2850_, v___x_2851_, v___x_2838_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_args_2831_);
return v___x_2852_;
}
}
}
}
else
{
lean_dec_ref(v_args_2831_);
lean_dec_ref(v_f_2817_);
return v___x_2832_;
}
}
case 4:
{
lean_object* v_cases_2855_; lean_object* v_resultType_2856_; lean_object* v_discr_2857_; lean_object* v_alts_2858_; lean_object* v___x_2859_; 
v_cases_2855_ = lean_ctor_get(v_c_2818_, 0);
lean_inc_ref(v_cases_2855_);
lean_dec_ref_known(v_c_2818_, 1);
v_resultType_2856_ = lean_ctor_get(v_cases_2855_, 1);
lean_inc_ref(v_resultType_2856_);
v_discr_2857_ = lean_ctor_get(v_cases_2855_, 2);
lean_inc(v_discr_2857_);
v_alts_2858_ = lean_ctor_get(v_cases_2855_, 3);
lean_inc_ref(v_alts_2858_);
lean_dec_ref(v_cases_2855_);
lean_inc_ref(v_f_2817_);
v___x_2859_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2817_, v_resultType_2856_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref_known(v___x_2859_, 1);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2860_ = lean_apply_8(v_f_2817_, v_discr_2857_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2881_; 
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2860_, 0);
lean_dec(v_unused_2882_);
v___x_2862_ = v___x_2860_;
v_isShared_2863_ = v_isSharedCheck_2881_;
goto v_resetjp_2861_;
}
else
{
lean_dec(v___x_2860_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2881_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2864_ = lean_unsigned_to_nat(0u);
v___x_2865_ = lean_array_get_size(v_alts_2858_);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_nat_dec_lt(v___x_2864_, v___x_2865_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2869_; 
lean_dec_ref(v_alts_2858_);
lean_dec_ref(v_f_2817_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2866_);
v___x_2869_ = v___x_2862_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2866_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
else
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_nat_dec_le(v___x_2865_, v___x_2865_);
if (v___x_2871_ == 0)
{
if (v___x_2867_ == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref(v_alts_2858_);
lean_dec_ref(v_f_2817_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2866_);
v___x_2873_ = v___x_2862_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2866_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
else
{
size_t v___x_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
lean_del_object(v___x_2862_);
v___x_2875_ = ((size_t)0ULL);
v___x_2876_ = lean_usize_of_nat(v___x_2865_);
v___x_2877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2816_, v_f_2817_, v_alts_2858_, v___x_2875_, v___x_2876_, v___x_2866_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_alts_2858_);
return v___x_2877_;
}
}
else
{
size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2862_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = lean_usize_of_nat(v___x_2865_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2816_, v_f_2817_, v_alts_2858_, v___x_2878_, v___x_2879_, v___x_2866_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_alts_2858_);
return v___x_2880_;
}
}
}
}
else
{
lean_dec_ref(v_alts_2858_);
lean_dec_ref(v_f_2817_);
return v___x_2860_;
}
}
else
{
lean_dec_ref(v_alts_2858_);
lean_dec(v_discr_2857_);
lean_dec_ref(v_f_2817_);
return v___x_2859_;
}
}
case 5:
{
lean_object* v_fvarId_2883_; lean_object* v___x_2884_; 
v_fvarId_2883_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2883_);
lean_dec_ref_known(v_c_2818_, 1);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2884_ = lean_apply_8(v_f_2817_, v_fvarId_2883_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
return v___x_2884_;
}
case 6:
{
lean_object* v_type_2885_; lean_object* v___x_2886_; 
v_type_2885_ = lean_ctor_get(v_c_2818_, 0);
lean_inc_ref(v_type_2885_);
lean_dec_ref_known(v_c_2818_, 1);
v___x_2886_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2817_, v_type_2885_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2886_;
}
case 7:
{
lean_object* v_fvarId_2887_; lean_object* v_y_2888_; lean_object* v_k_2889_; lean_object* v___x_2890_; 
v_fvarId_2887_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2887_);
v_y_2888_ = lean_ctor_get(v_c_2818_, 2);
lean_inc(v_y_2888_);
v_k_2889_ = lean_ctor_get(v_c_2818_, 3);
lean_inc_ref(v_k_2889_);
lean_dec_ref_known(v_c_2818_, 4);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2890_ = lean_apply_8(v_f_2817_, v_fvarId_2887_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; 
lean_dec_ref_known(v___x_2890_, 1);
lean_inc_ref(v_f_2817_);
v___x_2891_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2817_, v_y_2888_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_dec_ref_known(v___x_2891_, 1);
v_c_2818_ = v_k_2889_;
goto _start;
}
else
{
lean_dec_ref(v_k_2889_);
lean_dec_ref(v_f_2817_);
return v___x_2891_;
}
}
else
{
lean_dec_ref(v_k_2889_);
lean_dec(v_y_2888_);
lean_dec_ref(v_f_2817_);
return v___x_2890_;
}
}
case 8:
{
lean_object* v_fvarId_2893_; lean_object* v_y_2894_; lean_object* v_k_2895_; lean_object* v___x_2896_; 
v_fvarId_2893_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2893_);
v_y_2894_ = lean_ctor_get(v_c_2818_, 2);
lean_inc(v_y_2894_);
v_k_2895_ = lean_ctor_get(v_c_2818_, 3);
lean_inc_ref(v_k_2895_);
lean_dec_ref_known(v_c_2818_, 4);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2896_ = lean_apply_8(v_f_2817_, v_fvarId_2893_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2897_; 
lean_dec_ref_known(v___x_2896_, 1);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2897_ = lean_apply_8(v_f_2817_, v_y_2894_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref_known(v___x_2897_, 1);
v_c_2818_ = v_k_2895_;
goto _start;
}
else
{
lean_dec_ref(v_k_2895_);
lean_dec_ref(v_f_2817_);
return v___x_2897_;
}
}
else
{
lean_dec_ref(v_k_2895_);
lean_dec(v_y_2894_);
lean_dec_ref(v_f_2817_);
return v___x_2896_;
}
}
case 9:
{
lean_object* v_fvarId_2899_; lean_object* v_y_2900_; lean_object* v_ty_2901_; lean_object* v_k_2902_; lean_object* v___x_2903_; 
v_fvarId_2899_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2899_);
v_y_2900_ = lean_ctor_get(v_c_2818_, 3);
lean_inc(v_y_2900_);
v_ty_2901_ = lean_ctor_get(v_c_2818_, 4);
lean_inc_ref(v_ty_2901_);
v_k_2902_ = lean_ctor_get(v_c_2818_, 5);
lean_inc_ref(v_k_2902_);
lean_dec_ref_known(v_c_2818_, 6);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2903_ = lean_apply_8(v_f_2817_, v_fvarId_2899_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2904_; 
lean_dec_ref_known(v___x_2903_, 1);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2904_ = lean_apply_8(v_f_2817_, v_y_2900_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; 
lean_dec_ref_known(v___x_2904_, 1);
lean_inc_ref(v_f_2817_);
v___x_2905_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2817_, v_ty_2901_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_dec_ref_known(v___x_2905_, 1);
v_c_2818_ = v_k_2902_;
goto _start;
}
else
{
lean_dec_ref(v_k_2902_);
lean_dec_ref(v_f_2817_);
return v___x_2905_;
}
}
else
{
lean_dec_ref(v_k_2902_);
lean_dec_ref(v_ty_2901_);
lean_dec_ref(v_f_2817_);
return v___x_2904_;
}
}
else
{
lean_dec_ref(v_k_2902_);
lean_dec_ref(v_ty_2901_);
lean_dec(v_y_2900_);
lean_dec_ref(v_f_2817_);
return v___x_2903_;
}
}
case 10:
{
lean_object* v_fvarId_2907_; lean_object* v_k_2908_; lean_object* v___x_2909_; 
v_fvarId_2907_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2907_);
v_k_2908_ = lean_ctor_get(v_c_2818_, 2);
lean_inc_ref(v_k_2908_);
lean_dec_ref_known(v_c_2818_, 3);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2909_ = lean_apply_8(v_f_2817_, v_fvarId_2907_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_dec_ref_known(v___x_2909_, 1);
v_c_2818_ = v_k_2908_;
goto _start;
}
else
{
lean_dec_ref(v_k_2908_);
lean_dec_ref(v_f_2817_);
return v___x_2909_;
}
}
case 11:
{
lean_object* v_fvarId_2911_; lean_object* v_k_2912_; lean_object* v___x_2913_; 
v_fvarId_2911_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2911_);
v_k_2912_ = lean_ctor_get(v_c_2818_, 2);
lean_inc_ref(v_k_2912_);
lean_dec_ref_known(v_c_2818_, 3);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2913_ = lean_apply_8(v_f_2817_, v_fvarId_2911_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref_known(v___x_2913_, 1);
v_c_2818_ = v_k_2912_;
goto _start;
}
else
{
lean_dec_ref(v_k_2912_);
lean_dec_ref(v_f_2817_);
return v___x_2913_;
}
}
case 12:
{
lean_object* v_fvarId_2915_; lean_object* v_k_2916_; lean_object* v___x_2917_; 
v_fvarId_2915_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2915_);
v_k_2916_ = lean_ctor_get(v_c_2818_, 3);
lean_inc_ref(v_k_2916_);
lean_dec_ref_known(v_c_2818_, 4);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2917_ = lean_apply_8(v_f_2817_, v_fvarId_2915_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_dec_ref_known(v___x_2917_, 1);
v_c_2818_ = v_k_2916_;
goto _start;
}
else
{
lean_dec_ref(v_k_2916_);
lean_dec_ref(v_f_2817_);
return v___x_2917_;
}
}
case 13:
{
lean_object* v_fvarId_2919_; lean_object* v_k_2920_; lean_object* v___x_2921_; 
v_fvarId_2919_ = lean_ctor_get(v_c_2818_, 0);
lean_inc(v_fvarId_2919_);
v_k_2920_ = lean_ctor_get(v_c_2818_, 1);
lean_inc_ref(v_k_2920_);
lean_dec_ref_known(v_c_2818_, 2);
lean_inc_ref(v_f_2817_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___y_2819_);
v___x_2921_ = lean_apply_8(v_f_2817_, v_fvarId_2919_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, lean_box(0));
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_dec_ref_known(v___x_2921_, 1);
v_c_2818_ = v_k_2920_;
goto _start;
}
else
{
lean_dec_ref(v_k_2920_);
lean_dec_ref(v_f_2817_);
return v___x_2921_;
}
}
default: 
{
lean_object* v_decl_2923_; lean_object* v_k_2924_; lean_object* v_params_2925_; lean_object* v_type_2926_; lean_object* v_value_2927_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_decl_2923_ = lean_ctor_get(v_c_2818_, 0);
lean_inc_ref(v_decl_2923_);
v_k_2924_ = lean_ctor_get(v_c_2818_, 1);
lean_inc_ref(v_k_2924_);
lean_dec_ref(v_c_2818_);
v_params_2925_ = lean_ctor_get(v_decl_2923_, 2);
lean_inc_ref(v_params_2925_);
v_type_2926_ = lean_ctor_get(v_decl_2923_, 3);
lean_inc_ref(v_type_2926_);
v_value_2927_ = lean_ctor_get(v_decl_2923_, 4);
lean_inc_ref(v_value_2927_);
lean_dec_ref(v_decl_2923_);
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_2939_ = lean_array_get_size(v_params_2925_);
v___x_2940_ = lean_nat_dec_lt(v___x_2938_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; 
lean_dec_ref(v_params_2925_);
lean_inc_ref(v_f_2817_);
v___x_2941_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2817_, v_type_2926_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref_known(v___x_2941_, 1);
lean_inc_ref(v_f_2817_);
v___x_2942_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2816_, v_f_2817_, v_value_2927_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_dec_ref_known(v___x_2942_, 1);
v_c_2818_ = v_k_2924_;
goto _start;
}
else
{
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2817_);
return v___x_2942_;
}
}
else
{
lean_dec_ref(v_value_2927_);
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2817_);
return v___x_2941_;
}
}
else
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_nat_dec_le(v___x_2939_, v___x_2939_);
if (v___x_2945_ == 0)
{
if (v___x_2940_ == 0)
{
lean_dec_ref(v_params_2925_);
v___y_2929_ = v___y_2819_;
v___y_2930_ = v___y_2820_;
v___y_2931_ = v___y_2821_;
v___y_2932_ = v___y_2822_;
v___y_2933_ = v___y_2823_;
v___y_2934_ = v___y_2824_;
goto v___jp_2928_;
}
else
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___x_2939_);
lean_inc_ref(v_f_2817_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2816_, v_f_2817_, v_params_2925_, v___x_2946_, v___x_2947_, v___x_2944_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_params_2925_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_dec_ref_known(v___x_2948_, 1);
v___y_2929_ = v___y_2819_;
v___y_2930_ = v___y_2820_;
v___y_2931_ = v___y_2821_;
v___y_2932_ = v___y_2822_;
v___y_2933_ = v___y_2823_;
v___y_2934_ = v___y_2824_;
goto v___jp_2928_;
}
else
{
lean_dec_ref(v_value_2927_);
lean_dec_ref(v_type_2926_);
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2817_);
return v___x_2948_;
}
}
}
else
{
size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___x_2939_);
lean_inc_ref(v_f_2817_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2816_, v_f_2817_, v_params_2925_, v___x_2949_, v___x_2950_, v___x_2944_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_params_2925_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_dec_ref_known(v___x_2951_, 1);
v___y_2929_ = v___y_2819_;
v___y_2930_ = v___y_2820_;
v___y_2931_ = v___y_2821_;
v___y_2932_ = v___y_2822_;
v___y_2933_ = v___y_2823_;
v___y_2934_ = v___y_2824_;
goto v___jp_2928_;
}
else
{
lean_dec_ref(v_value_2927_);
lean_dec_ref(v_type_2926_);
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2817_);
return v___x_2951_;
}
}
}
v___jp_2928_:
{
lean_object* v___x_2935_; 
lean_inc_ref(v_f_2817_);
v___x_2935_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2817_, v_type_2926_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2935_, 1);
lean_inc_ref(v_f_2817_);
v___x_2936_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2816_, v_f_2817_, v_value_2927_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_dec_ref_known(v___x_2936_, 1);
v_c_2818_ = v_k_2924_;
v___y_2819_ = v___y_2929_;
v___y_2820_ = v___y_2930_;
v___y_2821_ = v___y_2931_;
v___y_2822_ = v___y_2932_;
v___y_2823_ = v___y_2933_;
v___y_2824_ = v___y_2934_;
goto _start;
}
else
{
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2817_);
return v___x_2936_;
}
}
else
{
lean_dec_ref(v_value_2927_);
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2817_);
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2952_, lean_object* v_f_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2952_, v_f_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_2963_, lean_object* v_f_2964_, lean_object* v_as_2965_, lean_object* v_i_2966_, lean_object* v_stop_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v_pu_boxed_2976_; size_t v_i_boxed_2977_; size_t v_stop_boxed_2978_; lean_object* v_res_2979_; 
v_pu_boxed_2976_ = lean_unbox(v_pu_2963_);
v_i_boxed_2977_ = lean_unbox_usize(v_i_2966_);
lean_dec(v_i_2966_);
v_stop_boxed_2978_ = lean_unbox_usize(v_stop_2967_);
lean_dec(v_stop_2967_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_2976_, v_f_2964_, v_as_2965_, v_i_boxed_2977_, v_stop_boxed_2978_, v_b_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v_as_2965_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_2980_, lean_object* v_f_2981_, lean_object* v_c_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
uint8_t v_pu_boxed_2990_; lean_object* v_res_2991_; 
v_pu_boxed_2990_ = lean_unbox(v_pu_2980_);
v_res_2991_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_2990_, v_f_2981_, v_c_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec(v___y_2983_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_2992_, lean_object* v_f_2993_, lean_object* v_decl_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_params_3002_; lean_object* v_type_3003_; lean_object* v_value_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_params_3002_ = lean_ctor_get(v_decl_2994_, 2);
lean_inc_ref(v_params_3002_);
v_type_3003_ = lean_ctor_get(v_decl_2994_, 3);
lean_inc_ref(v_type_3003_);
v_value_3004_ = lean_ctor_get(v_decl_2994_, 4);
lean_inc_ref(v_value_3004_);
lean_dec_ref(v_decl_2994_);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_array_get_size(v_params_3002_);
v___x_3016_ = lean_nat_dec_lt(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
lean_dec_ref(v_params_3002_);
lean_inc_ref(v_f_2993_);
v___x_3017_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2993_, v_type_3003_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3018_; 
lean_dec_ref_known(v___x_3017_, 1);
v___x_3018_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2992_, v_f_2993_, v_value_3004_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
return v___x_3018_;
}
else
{
lean_dec_ref(v_value_3004_);
lean_dec_ref(v_f_2993_);
return v___x_3017_;
}
}
else
{
lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = lean_box(0);
v___x_3020_ = lean_nat_dec_le(v___x_3015_, v___x_3015_);
if (v___x_3020_ == 0)
{
if (v___x_3016_ == 0)
{
lean_dec_ref(v_params_3002_);
v___y_3006_ = v___y_2995_;
v___y_3007_ = v___y_2996_;
v___y_3008_ = v___y_2997_;
v___y_3009_ = v___y_2998_;
v___y_3010_ = v___y_2999_;
v___y_3011_ = v___y_3000_;
goto v___jp_3005_;
}
else
{
size_t v___x_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = lean_usize_of_nat(v___x_3015_);
lean_inc_ref(v_f_2993_);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2992_, v_f_2993_, v_params_3002_, v___x_3021_, v___x_3022_, v___x_3019_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec_ref(v_params_3002_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_dec_ref_known(v___x_3023_, 1);
v___y_3006_ = v___y_2995_;
v___y_3007_ = v___y_2996_;
v___y_3008_ = v___y_2997_;
v___y_3009_ = v___y_2998_;
v___y_3010_ = v___y_2999_;
v___y_3011_ = v___y_3000_;
goto v___jp_3005_;
}
else
{
lean_dec_ref(v_value_3004_);
lean_dec_ref(v_type_3003_);
lean_dec_ref(v_f_2993_);
return v___x_3023_;
}
}
}
else
{
size_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = lean_usize_of_nat(v___x_3015_);
lean_inc_ref(v_f_2993_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2992_, v_f_2993_, v_params_3002_, v___x_3024_, v___x_3025_, v___x_3019_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec_ref(v_params_3002_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_dec_ref_known(v___x_3026_, 1);
v___y_3006_ = v___y_2995_;
v___y_3007_ = v___y_2996_;
v___y_3008_ = v___y_2997_;
v___y_3009_ = v___y_2998_;
v___y_3010_ = v___y_2999_;
v___y_3011_ = v___y_3000_;
goto v___jp_3005_;
}
else
{
lean_dec_ref(v_value_3004_);
lean_dec_ref(v_type_3003_);
lean_dec_ref(v_f_2993_);
return v___x_3026_;
}
}
}
v___jp_3005_:
{
lean_object* v___x_3012_; 
lean_inc_ref(v_f_2993_);
v___x_3012_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2993_, v_type_3003_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v___x_3013_; 
lean_dec_ref_known(v___x_3012_, 1);
v___x_3013_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2992_, v_f_2993_, v_value_3004_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3013_;
}
else
{
lean_dec_ref(v_value_3004_);
lean_dec_ref(v_f_2993_);
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_3027_, lean_object* v_f_3028_, lean_object* v_decl_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v_pu_boxed_3037_; lean_object* v_res_3038_; 
v_pu_boxed_3037_ = lean_unbox(v_pu_3027_);
v_res_3038_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_3037_, v_f_3028_, v_decl_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec(v___y_3030_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_3039_){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_panic_fn_borrowed(v___x_3040_, v_msg_3039_);
return v___x_3041_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3045_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_3046_ = lean_unsigned_to_nat(11u);
v___x_3047_ = lean_unsigned_to_nat(163u);
v___x_3048_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_3049_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_3050_ = l_mkPanicMessageWithDecl(v___x_3049_, v___x_3048_, v___x_3047_, v___x_3046_, v___x_3045_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_3051_, lean_object* v_x_3052_){
_start:
{
if (lean_obj_tag(v_x_3052_) == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3054_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_3053_);
return v___x_3054_;
}
else
{
lean_object* v_key_3055_; lean_object* v_value_3056_; lean_object* v_tail_3057_; uint8_t v___x_3058_; 
v_key_3055_ = lean_ctor_get(v_x_3052_, 0);
v_value_3056_ = lean_ctor_get(v_x_3052_, 1);
v_tail_3057_ = lean_ctor_get(v_x_3052_, 2);
v___x_3058_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_3055_, v_a_3051_);
if (v___x_3058_ == 0)
{
v_x_3052_ = v_tail_3057_;
goto _start;
}
else
{
lean_inc(v_value_3056_);
return v_value_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_3060_, lean_object* v_x_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3060_, v_x_3061_);
lean_dec(v_x_3061_);
lean_dec(v_a_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_buckets_3065_; lean_object* v___x_3066_; uint64_t v___x_3067_; uint64_t v___x_3068_; uint64_t v___x_3069_; uint64_t v_fold_3070_; uint64_t v___x_3071_; uint64_t v___x_3072_; uint64_t v___x_3073_; size_t v___x_3074_; size_t v___x_3075_; size_t v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_buckets_3065_ = lean_ctor_get(v_m_3063_, 1);
v___x_3066_ = lean_array_get_size(v_buckets_3065_);
v___x_3067_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_3064_);
v___x_3068_ = 32ULL;
v___x_3069_ = lean_uint64_shift_right(v___x_3067_, v___x_3068_);
v_fold_3070_ = lean_uint64_xor(v___x_3067_, v___x_3069_);
v___x_3071_ = 16ULL;
v___x_3072_ = lean_uint64_shift_right(v_fold_3070_, v___x_3071_);
v___x_3073_ = lean_uint64_xor(v_fold_3070_, v___x_3072_);
v___x_3074_ = lean_uint64_to_usize(v___x_3073_);
v___x_3075_ = lean_usize_of_nat(v___x_3066_);
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_sub(v___x_3075_, v___x_3076_);
v___x_3078_ = lean_usize_land(v___x_3074_, v___x_3077_);
v___x_3079_ = lean_array_uget_borrowed(v_buckets_3065_, v___x_3078_);
v___x_3080_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3064_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3081_, v_a_3082_);
lean_dec(v_a_3082_);
lean_dec_ref(v_m_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___y_3094_; uint8_t v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = 0;
v___x_3120_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3085_))
{
case 0:
{
lean_object* v_decl_3121_; lean_object* v___x_3122_; 
v_decl_3121_ = lean_ctor_get(v_decl_3085_, 0);
lean_inc_ref(v_decl_3121_);
v___x_3122_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3119_, v___x_3120_, v_decl_3121_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
v___y_3094_ = v___x_3122_;
goto v___jp_3093_;
}
case 1:
{
lean_object* v_decl_3123_; lean_object* v___x_3124_; 
v_decl_3123_ = lean_ctor_get(v_decl_3085_, 0);
lean_inc_ref(v_decl_3123_);
v___x_3124_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3119_, v___x_3120_, v_decl_3123_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
v___y_3094_ = v___x_3124_;
goto v___jp_3093_;
}
case 2:
{
lean_object* v_decl_3125_; lean_object* v___x_3126_; 
v_decl_3125_ = lean_ctor_get(v_decl_3085_, 0);
lean_inc_ref(v_decl_3125_);
v___x_3126_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3119_, v___x_3120_, v_decl_3125_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
v___y_3094_ = v___x_3126_;
goto v___jp_3093_;
}
case 3:
{
lean_object* v_fvarId_3127_; lean_object* v_y_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_fvarId_3127_ = lean_ctor_get(v_decl_3085_, 0);
v_y_3128_ = lean_ctor_get(v_decl_3085_, 2);
lean_inc(v_fvarId_3127_);
v___x_3129_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3127_, v_a_3086_);
lean_dec_ref(v___x_3129_);
lean_inc(v_y_3128_);
v___x_3130_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3120_, v_y_3128_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
v___y_3094_ = v___x_3130_;
goto v___jp_3093_;
}
case 4:
{
lean_object* v_fvarId_3131_; lean_object* v_y_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_fvarId_3131_ = lean_ctor_get(v_decl_3085_, 0);
v_y_3132_ = lean_ctor_get(v_decl_3085_, 2);
lean_inc(v_fvarId_3131_);
v___x_3133_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3131_, v_a_3086_);
lean_dec_ref(v___x_3133_);
lean_inc(v_y_3132_);
v___x_3134_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3132_, v_a_3086_);
v___y_3094_ = v___x_3134_;
goto v___jp_3093_;
}
case 5:
{
lean_object* v_fvarId_3135_; lean_object* v_y_3136_; lean_object* v_ty_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_fvarId_3135_ = lean_ctor_get(v_decl_3085_, 0);
v_y_3136_ = lean_ctor_get(v_decl_3085_, 3);
v_ty_3137_ = lean_ctor_get(v_decl_3085_, 4);
lean_inc(v_fvarId_3135_);
v___x_3138_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3135_, v_a_3086_);
lean_dec_ref(v___x_3138_);
lean_inc(v_y_3136_);
v___x_3139_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3136_, v_a_3086_);
lean_dec_ref(v___x_3139_);
lean_inc_ref(v_ty_3137_);
v___x_3140_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3120_, v_ty_3137_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
v___y_3094_ = v___x_3140_;
goto v___jp_3093_;
}
default: 
{
lean_object* v_fvarId_3141_; lean_object* v___x_3142_; 
v_fvarId_3141_ = lean_ctor_get(v_decl_3085_, 0);
lean_inc(v_fvarId_3141_);
v___x_3142_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3141_, v_a_3086_);
v___y_3094_ = v___x_3142_;
goto v___jp_3093_;
}
}
v___jp_3093_:
{
if (lean_obj_tag(v___y_3094_) == 0)
{
lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___y_3094_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___y_3094_, 0);
lean_dec(v_unused_3118_);
v___x_3096_ = v___y_3094_;
v_isShared_3097_ = v_isSharedCheck_3117_;
goto v_resetjp_3095_;
}
else
{
lean_dec(v___y_3094_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3117_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v_decision_3099_; lean_object* v_newArms_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3116_; 
v___x_3098_ = lean_st_ref_take(v_a_3086_);
v_decision_3099_ = lean_ctor_get(v___x_3098_, 0);
v_newArms_3100_ = lean_ctor_get(v___x_3098_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3102_ = v___x_3098_;
v_isShared_3103_ = v_isSharedCheck_3116_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_newArms_3100_);
lean_inc(v_decision_3099_);
lean_dec(v___x_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3116_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3104_ = lean_box(2);
v___x_3105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3100_, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_decl_3085_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3100_, v___x_3104_, v___x_3106_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v___x_3107_);
v___x_3109_ = v___x_3102_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_decision_3099_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3110_ = lean_st_ref_set(v_a_3086_, v___x_3109_);
v___x_3111_ = lean_box(0);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3111_);
v___x_3113_ = v___x_3096_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3085_);
return v___y_3094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec(v_a_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3152_, lean_object* v_f_3153_, lean_object* v_arg_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3153_, v_arg_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3163_, lean_object* v_f_3164_, lean_object* v_arg_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
uint8_t v_pu_boxed_3173_; lean_object* v_res_3174_; 
v_pu_boxed_3173_ = lean_unbox(v_pu_3163_);
v_res_3174_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3173_, v_f_3164_, v_arg_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec(v___y_3166_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3175_, lean_object* v_f_3176_, lean_object* v_param_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3176_, v_param_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3186_, lean_object* v_f_3187_, lean_object* v_param_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
uint8_t v_pu_boxed_3196_; lean_object* v_res_3197_; 
v_pu_boxed_3196_ = lean_unbox(v_pu_3186_);
v_res_3197_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3196_, v_f_3187_, v_param_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec(v___y_3189_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3198_, lean_object* v_alt_3199_, lean_object* v_f_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3199_, v_f_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3209_, lean_object* v_alt_3210_, lean_object* v_f_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v_pu_boxed_3219_; lean_object* v_res_3220_; 
v_pu_boxed_3219_ = lean_unbox(v_pu_3209_);
v_res_3220_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3219_, v_alt_3210_, v_f_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec(v___y_3212_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3221_, lean_object* v_arm_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3225_; lean_object* v_decision_3242_; lean_object* v___x_3243_; 
v___x_3225_ = lean_st_ref_get(v_a_3223_);
v_decision_3242_ = lean_ctor_get(v___x_3225_, 0);
lean_inc_ref(v_decision_3242_);
lean_dec(v___x_3225_);
v___x_3243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3242_, v_fvar_3221_);
lean_dec_ref(v_decision_3242_);
if (lean_obj_tag(v___x_3243_) == 1)
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3271_; 
v_val_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3271_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3271_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = lean_box(3);
v___x_3249_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3244_, v___x_3248_);
if (v___x_3249_ == 0)
{
uint8_t v___x_3250_; 
v___x_3250_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3244_, v_arm_3222_);
lean_dec(v_arm_3222_);
lean_dec(v_val_3244_);
if (v___x_3250_ == 0)
{
lean_del_object(v___x_3246_);
goto v___jp_3226_;
}
else
{
if (v___x_3249_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
lean_dec(v_fvar_3221_);
v___x_3251_ = lean_box(0);
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3251_);
v___x_3253_ = v___x_3246_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
else
{
lean_del_object(v___x_3246_);
goto v___jp_3226_;
}
}
}
else
{
lean_object* v___x_3255_; lean_object* v_decision_3256_; lean_object* v_newArms_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v_val_3244_);
v___x_3255_ = lean_st_ref_take(v_a_3223_);
v_decision_3256_ = lean_ctor_get(v___x_3255_, 0);
v_newArms_3257_ = lean_ctor_get(v___x_3255_, 1);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3259_ = v___x_3255_;
v_isShared_3260_ = v_isSharedCheck_3270_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_newArms_3257_);
lean_inc(v_decision_3256_);
lean_dec(v___x_3255_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3270_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3256_, v_fvar_3221_, v_arm_3222_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3261_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v_newArms_3257_);
v___x_3263_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3264_ = lean_st_ref_set(v_a_3223_, v___x_3263_);
v___x_3265_ = lean_box(0);
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3265_);
v___x_3267_ = v___x_3246_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v___x_3243_);
lean_dec(v_arm_3222_);
lean_dec(v_fvar_3221_);
v___x_3272_ = lean_box(0);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
v___jp_3226_:
{
lean_object* v___x_3227_; lean_object* v_decision_3228_; lean_object* v_newArms_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3241_; 
v___x_3227_ = lean_st_ref_take(v_a_3223_);
v_decision_3228_ = lean_ctor_get(v___x_3227_, 0);
v_newArms_3229_ = lean_ctor_get(v___x_3227_, 1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3231_ = v___x_3227_;
v_isShared_3232_ = v_isSharedCheck_3241_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_newArms_3229_);
lean_inc(v_decision_3228_);
lean_dec(v___x_3227_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3241_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = lean_box(2);
v___x_3234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3228_, v_fvar_3221_, v___x_3233_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_newArms_3229_);
v___x_3236_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_st_ref_set(v_a_3223_, v___x_3236_);
v___x_3238_ = lean_box(0);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3274_, lean_object* v_arm_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3274_, v_arm_3275_, v_a_3276_);
lean_dec(v_a_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3279_, lean_object* v_arm_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3279_, v_arm_3280_, v_a_3281_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3289_, lean_object* v_arm_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3289_, v_arm_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec(v_a_3291_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3300_, v___x_3299_, v___y_3301_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3309_, v_x_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3311_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3321_ = lean_panic_fn_borrowed(v___x_3320_, v_msg_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3322_, lean_object* v_x_3323_){
_start:
{
if (lean_obj_tag(v_x_3323_) == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3325_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3324_);
return v___x_3325_;
}
else
{
lean_object* v_key_3326_; lean_object* v_value_3327_; lean_object* v_tail_3328_; uint8_t v___x_3329_; 
v_key_3326_ = lean_ctor_get(v_x_3323_, 0);
v_value_3327_ = lean_ctor_get(v_x_3323_, 1);
v_tail_3328_ = lean_ctor_get(v_x_3323_, 2);
v___x_3329_ = l_Lean_instBEqFVarId_beq(v_key_3326_, v_a_3322_);
if (v___x_3329_ == 0)
{
v_x_3323_ = v_tail_3328_;
goto _start;
}
else
{
lean_inc(v_value_3327_);
return v_value_3327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3331_, v_x_3332_);
lean_dec(v_x_3332_);
lean_dec(v_a_3331_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_buckets_3336_; lean_object* v___x_3337_; uint64_t v___x_3338_; uint64_t v___x_3339_; uint64_t v___x_3340_; uint64_t v_fold_3341_; uint64_t v___x_3342_; uint64_t v___x_3343_; uint64_t v___x_3344_; size_t v___x_3345_; size_t v___x_3346_; size_t v___x_3347_; size_t v___x_3348_; size_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_buckets_3336_ = lean_ctor_get(v_m_3334_, 1);
v___x_3337_ = lean_array_get_size(v_buckets_3336_);
v___x_3338_ = l_Lean_instHashableFVarId_hash(v_a_3335_);
v___x_3339_ = 32ULL;
v___x_3340_ = lean_uint64_shift_right(v___x_3338_, v___x_3339_);
v_fold_3341_ = lean_uint64_xor(v___x_3338_, v___x_3340_);
v___x_3342_ = 16ULL;
v___x_3343_ = lean_uint64_shift_right(v_fold_3341_, v___x_3342_);
v___x_3344_ = lean_uint64_xor(v_fold_3341_, v___x_3343_);
v___x_3345_ = lean_uint64_to_usize(v___x_3344_);
v___x_3346_ = lean_usize_of_nat(v___x_3337_);
v___x_3347_ = ((size_t)1ULL);
v___x_3348_ = lean_usize_sub(v___x_3346_, v___x_3347_);
v___x_3349_ = lean_usize_land(v___x_3345_, v___x_3348_);
v___x_3350_ = lean_array_uget_borrowed(v_buckets_3336_, v___x_3349_);
v___x_3351_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3335_, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_m_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___x_3363_; lean_object* v_decision_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3421_; 
v___x_3363_ = lean_st_ref_get(v_a_3356_);
v_decision_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v___x_3363_, 1);
lean_dec(v_unused_3422_);
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3421_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_decision_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3421_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___y_3372_; lean_object* v___f_3398_; 
v___x_3368_ = 0;
v___x_3369_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3355_);
v___x_3370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3364_, v___x_3369_);
lean_dec(v___x_3369_);
lean_dec_ref(v_decision_3364_);
lean_inc(v___x_3370_);
v___f_3398_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3398_, 0, v___x_3370_);
switch(lean_obj_tag(v_decl_3355_))
{
case 0:
{
lean_object* v_decl_3399_; lean_object* v___x_3400_; 
v_decl_3399_ = lean_ctor_get(v_decl_3355_, 0);
lean_inc_ref(v_decl_3399_);
v___x_3400_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3368_, v___f_3398_, v_decl_3399_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
v___y_3372_ = v___x_3400_;
goto v___jp_3371_;
}
case 1:
{
lean_object* v_decl_3401_; lean_object* v___x_3402_; 
v_decl_3401_ = lean_ctor_get(v_decl_3355_, 0);
lean_inc_ref(v_decl_3401_);
v___x_3402_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3368_, v___f_3398_, v_decl_3401_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
v___y_3372_ = v___x_3402_;
goto v___jp_3371_;
}
case 2:
{
lean_object* v_decl_3403_; lean_object* v___x_3404_; 
v_decl_3403_ = lean_ctor_get(v_decl_3355_, 0);
lean_inc_ref(v_decl_3403_);
v___x_3404_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3368_, v___f_3398_, v_decl_3403_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
v___y_3372_ = v___x_3404_;
goto v___jp_3371_;
}
case 3:
{
lean_object* v_fvarId_3405_; lean_object* v_y_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_fvarId_3405_ = lean_ctor_get(v_decl_3355_, 0);
v_y_3406_ = lean_ctor_get(v_decl_3355_, 2);
lean_inc(v___x_3370_);
lean_inc(v_fvarId_3405_);
v___x_3407_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3405_, v___x_3370_, v_a_3356_);
lean_dec_ref(v___x_3407_);
lean_inc(v_y_3406_);
v___x_3408_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3398_, v_y_3406_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
v___y_3372_ = v___x_3408_;
goto v___jp_3371_;
}
case 4:
{
lean_object* v_fvarId_3409_; lean_object* v_y_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec_ref(v___f_3398_);
v_fvarId_3409_ = lean_ctor_get(v_decl_3355_, 0);
v_y_3410_ = lean_ctor_get(v_decl_3355_, 2);
lean_inc_n(v___x_3370_, 2);
lean_inc(v_fvarId_3409_);
v___x_3411_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3409_, v___x_3370_, v_a_3356_);
lean_dec_ref(v___x_3411_);
lean_inc(v_y_3410_);
v___x_3412_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3410_, v___x_3370_, v_a_3356_);
v___y_3372_ = v___x_3412_;
goto v___jp_3371_;
}
case 5:
{
lean_object* v_fvarId_3413_; lean_object* v_y_3414_; lean_object* v_ty_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_fvarId_3413_ = lean_ctor_get(v_decl_3355_, 0);
v_y_3414_ = lean_ctor_get(v_decl_3355_, 3);
v_ty_3415_ = lean_ctor_get(v_decl_3355_, 4);
lean_inc_n(v___x_3370_, 2);
lean_inc(v_fvarId_3413_);
v___x_3416_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3413_, v___x_3370_, v_a_3356_);
lean_dec_ref(v___x_3416_);
lean_inc(v_y_3414_);
v___x_3417_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3414_, v___x_3370_, v_a_3356_);
lean_dec_ref(v___x_3417_);
lean_inc_ref(v_ty_3415_);
v___x_3418_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3398_, v_ty_3415_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
v___y_3372_ = v___x_3418_;
goto v___jp_3371_;
}
default: 
{
lean_object* v_fvarId_3419_; lean_object* v___x_3420_; 
lean_dec_ref(v___f_3398_);
v_fvarId_3419_ = lean_ctor_get(v_decl_3355_, 0);
lean_inc(v___x_3370_);
lean_inc(v_fvarId_3419_);
v___x_3420_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3419_, v___x_3370_, v_a_3356_);
v___y_3372_ = v___x_3420_;
goto v___jp_3371_;
}
}
v___jp_3371_:
{
if (lean_obj_tag(v___y_3372_) == 0)
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3396_; 
v_isSharedCheck_3396_ = !lean_is_exclusive(v___y_3372_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v___y_3372_, 0);
lean_dec(v_unused_3397_);
v___x_3374_ = v___y_3372_;
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v___y_3372_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v_decision_3377_; lean_object* v_newArms_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3395_; 
v___x_3376_ = lean_st_ref_take(v_a_3356_);
v_decision_3377_ = lean_ctor_get(v___x_3376_, 0);
v_newArms_3378_ = lean_ctor_get(v___x_3376_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3380_ = v___x_3376_;
v_isShared_3381_ = v_isSharedCheck_3395_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_newArms_3378_);
lean_inc(v_decision_3377_);
lean_dec(v___x_3376_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3395_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3378_, v___x_3370_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 1);
lean_ctor_set(v___x_3366_, 1, v___x_3382_);
lean_ctor_set(v___x_3366_, 0, v_decl_3355_);
v___x_3384_ = v___x_3366_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_decl_3355_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3378_, v___x_3370_, v___x_3384_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 1, v___x_3385_);
v___x_3387_ = v___x_3380_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_decision_3377_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3388_ = lean_st_ref_set(v_a_3356_, v___x_3387_);
v___x_3389_ = lean_box(0);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3389_);
v___x_3391_ = v___x_3374_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3370_);
lean_del_object(v___x_3366_);
lean_dec_ref(v_decl_3355_);
return v___y_3372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
lean_dec(v_a_3425_);
lean_dec(v_a_3424_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3432_, lean_object* v_b_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
if (lean_obj_tag(v_as_x27_3432_) == 0)
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_b_3433_);
return v___x_3441_;
}
else
{
lean_object* v_head_3442_; lean_object* v_tail_3443_; lean_object* v___x_3444_; lean_object* v_decision_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v_head_3442_ = lean_ctor_get(v_as_x27_3432_, 0);
v_tail_3443_ = lean_ctor_get(v_as_x27_3432_, 1);
v___x_3444_ = lean_st_ref_get(v___y_3434_);
v_decision_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_ref(v_decision_3445_);
lean_dec(v___x_3444_);
v___x_3446_ = lean_box(0);
v___x_3447_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3442_);
v___x_3448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3445_, v___x_3447_);
lean_dec(v___x_3447_);
lean_dec_ref(v_decision_3445_);
v___x_3449_ = lean_box(3);
v___x_3450_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3451_ = lean_box(2);
v___x_3452_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3448_, v___x_3451_);
lean_dec(v___x_3448_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
lean_inc(v_head_3442_);
v___x_3453_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3442_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_dec_ref_known(v___x_3453_, 1);
v_as_x27_3432_ = v_tail_3443_;
v_b_3433_ = v___x_3446_;
goto _start;
}
else
{
return v___x_3453_;
}
}
else
{
lean_object* v___x_3455_; 
lean_inc(v_head_3442_);
v___x_3455_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3442_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec_ref_known(v___x_3455_, 1);
v_as_x27_3432_ = v_tail_3443_;
v_b_3433_ = v___x_3446_;
goto _start;
}
else
{
return v___x_3455_;
}
}
}
else
{
uint8_t v___x_3457_; lean_object* v___x_3458_; 
lean_dec(v___x_3448_);
v___x_3457_ = 0;
v___x_3458_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3457_, v_head_3442_, v___y_3437_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_dec_ref_known(v___x_3458_, 1);
v_as_x27_3432_ = v_tail_3443_;
v_b_3433_ = v___x_3446_;
goto _start;
}
else
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3460_, lean_object* v_b_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3460_, v_b_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec(v_as_x27_3460_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_box(0);
v___x_3478_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3471_, v___x_3477_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; 
v_unused_3486_ = lean_ctor_get(v___x_3478_, 0);
lean_dec(v_unused_3486_);
v___x_3480_ = v___x_3478_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_dec(v___x_3478_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3477_);
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3477_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
else
{
return v___x_3478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec(v_a_3487_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3495_, lean_object* v_as_x27_3496_, lean_object* v_b_3497_, lean_object* v_a_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3496_, v_b_3497_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_3507_, lean_object* v_as_x27_3508_, lean_object* v_b_3509_, lean_object* v_a_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3507_, v_as_x27_3508_, v_b_3509_, v_a_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec(v_as_x27_3508_);
lean_dec(v_as_3507_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
lean_ctor_set(v___x_3524_, 2, v___x_3523_);
lean_ctor_set(v___x_3524_, 3, v___x_3523_);
lean_ctor_set(v___x_3524_, 4, v___x_3522_);
lean_ctor_set(v___x_3524_, 5, v___x_3522_);
lean_ctor_set(v___x_3524_, 6, v___x_3522_);
lean_ctor_set(v___x_3524_, 7, v___x_3522_);
lean_ctor_set(v___x_3524_, 8, v___x_3522_);
lean_ctor_set(v___x_3524_, 9, v___x_3522_);
return v___x_3524_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3525_; double v___x_3526_; 
v___x_3525_ = lean_unsigned_to_nat(0u);
v___x_3526_ = lean_float_of_nat(v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3530_, lean_object* v_msg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_options_3537_; lean_object* v_ref_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_options_3537_ = lean_ctor_get(v___y_3534_, 2);
v_ref_3538_ = lean_ctor_get(v___y_3534_, 5);
v___x_3539_ = lean_st_ref_get(v___y_3535_);
v___x_3540_ = lean_st_ref_get(v___y_3533_);
v___x_3541_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3532_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3600_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3600_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3600_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v_env_3546_; lean_object* v_lctx_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3598_; 
v_env_3546_ = lean_ctor_get(v___x_3539_, 0);
lean_inc_ref(v_env_3546_);
lean_dec(v___x_3539_);
v_lctx_3547_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v___x_3540_, 1);
lean_dec(v_unused_3599_);
v___x_3549_ = v___x_3540_;
v_isShared_3550_ = v_isSharedCheck_3598_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_lctx_3547_);
lean_dec(v___x_3540_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3598_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v_traceState_3553_; lean_object* v_env_3554_; lean_object* v_nextMacroScope_3555_; lean_object* v_ngen_3556_; lean_object* v_auxDeclNGen_3557_; lean_object* v_cache_3558_; lean_object* v_messages_3559_; lean_object* v_infoState_3560_; lean_object* v_snapshotTasks_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3597_; 
v___x_3551_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3552_ = lean_st_ref_take(v___y_3535_);
v_traceState_3553_ = lean_ctor_get(v___x_3552_, 4);
v_env_3554_ = lean_ctor_get(v___x_3552_, 0);
v_nextMacroScope_3555_ = lean_ctor_get(v___x_3552_, 1);
v_ngen_3556_ = lean_ctor_get(v___x_3552_, 2);
v_auxDeclNGen_3557_ = lean_ctor_get(v___x_3552_, 3);
v_cache_3558_ = lean_ctor_get(v___x_3552_, 5);
v_messages_3559_ = lean_ctor_get(v___x_3552_, 6);
v_infoState_3560_ = lean_ctor_get(v___x_3552_, 7);
v_snapshotTasks_3561_ = lean_ctor_get(v___x_3552_, 8);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3563_ = v___x_3552_;
v_isShared_3564_ = v_isSharedCheck_3597_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_snapshotTasks_3561_);
lean_inc(v_infoState_3560_);
lean_inc(v_messages_3559_);
lean_inc(v_cache_3558_);
lean_inc(v_traceState_3553_);
lean_inc(v_auxDeclNGen_3557_);
lean_inc(v_ngen_3556_);
lean_inc(v_nextMacroScope_3555_);
lean_inc(v_env_3554_);
lean_dec(v___x_3552_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3597_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
uint64_t v_tid_3565_; lean_object* v_traces_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3596_; 
v_tid_3565_ = lean_ctor_get_uint64(v_traceState_3553_, sizeof(void*)*1);
v_traces_3566_ = lean_ctor_get(v_traceState_3553_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_traceState_3553_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3568_ = v_traceState_3553_;
v_isShared_3569_ = v_isSharedCheck_3596_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_traces_3566_);
lean_dec(v_traceState_3553_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3596_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3570_ = lean_unbox(v_a_3542_);
lean_dec(v_a_3542_);
v___x_3571_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3547_, v___x_3570_);
lean_dec_ref(v_lctx_3547_);
lean_inc_ref(v_options_3537_);
v___x_3572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3572_, 0, v_env_3546_);
lean_ctor_set(v___x_3572_, 1, v___x_3551_);
lean_ctor_set(v___x_3572_, 2, v___x_3571_);
lean_ctor_set(v___x_3572_, 3, v_options_3537_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set_tag(v___x_3549_, 3);
lean_ctor_set(v___x_3549_, 1, v_msg_3531_);
lean_ctor_set(v___x_3549_, 0, v___x_3572_);
v___x_3574_ = v___x_3549_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_msg_3531_);
v___x_3574_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; double v___x_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3575_ = lean_box(0);
v___x_3576_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3577_ = 0;
v___x_3578_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3579_, 0, v_cls_3530_);
lean_ctor_set(v___x_3579_, 1, v___x_3575_);
lean_ctor_set(v___x_3579_, 2, v___x_3578_);
lean_ctor_set_float(v___x_3579_, sizeof(void*)*3, v___x_3576_);
lean_ctor_set_float(v___x_3579_, sizeof(void*)*3 + 8, v___x_3576_);
lean_ctor_set_uint8(v___x_3579_, sizeof(void*)*3 + 16, v___x_3577_);
v___x_3580_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3581_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3574_);
lean_ctor_set(v___x_3581_, 2, v___x_3580_);
lean_inc(v_ref_3538_);
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_ref_3538_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = l_Lean_PersistentArray_push___redArg(v_traces_3566_, v___x_3582_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 0, v___x_3583_);
v___x_3585_ = v___x_3568_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3583_);
lean_ctor_set_uint64(v_reuseFailAlloc_3594_, sizeof(void*)*1, v_tid_3565_);
v___x_3585_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 4, v___x_3585_);
v___x_3587_ = v___x_3563_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_env_3554_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_nextMacroScope_3555_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_ngen_3556_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_auxDeclNGen_3557_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3593_, 5, v_cache_3558_);
lean_ctor_set(v_reuseFailAlloc_3593_, 6, v_messages_3559_);
lean_ctor_set(v_reuseFailAlloc_3593_, 7, v_infoState_3560_);
lean_ctor_set(v_reuseFailAlloc_3593_, 8, v_snapshotTasks_3561_);
v___x_3587_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3588_ = lean_st_ref_set(v___y_3535_, v___x_3587_);
v___x_3589_ = lean_box(0);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3589_);
v___x_3591_ = v___x_3544_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
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
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec(v___x_3540_);
lean_dec(v___x_3539_);
lean_dec_ref(v_msg_3531_);
lean_dec(v_cls_3530_);
v_a_3601_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3541_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3541_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3609_, lean_object* v_msg_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3609_, v_msg_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3617_, lean_object* v_msg_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3617_, v_msg_3618_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3626_, lean_object* v_msg_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3626_, v_msg_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
return v_res_3634_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3644_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3645_ = l_Lean_Name_append(v___x_3644_, v___x_3643_);
return v___x_3645_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3648_ = l_Lean_stringToMessageData(v___x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3651_ = l_Lean_stringToMessageData(v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
switch(lean_obj_tag(v_code_3652_))
{
case 0:
{
lean_object* v_decl_3659_; lean_object* v_k_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_decl_3659_ = lean_ctor_get(v_code_3652_, 0);
lean_inc_ref(v_decl_3659_);
v_k_3660_ = lean_ctor_get(v_code_3652_, 1);
lean_inc_ref(v_k_3660_);
lean_dec_ref_known(v_code_3652_, 2);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_decl_3659_);
v___x_3662_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3662_, 0, v_k_3660_);
v___x_3663_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3661_, v___x_3662_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
return v___x_3663_;
}
case 1:
{
lean_object* v_decl_3664_; lean_object* v_k_3665_; lean_object* v_params_3666_; lean_object* v_type_3667_; lean_object* v_value_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_decl_3664_ = lean_ctor_get(v_code_3652_, 0);
lean_inc_ref(v_decl_3664_);
v_k_3665_ = lean_ctor_get(v_code_3652_, 1);
lean_inc_ref(v_k_3665_);
lean_dec_ref_known(v_code_3652_, 2);
v_params_3666_ = lean_ctor_get(v_decl_3664_, 2);
lean_inc_ref(v_params_3666_);
v_type_3667_ = lean_ctor_get(v_decl_3664_, 3);
lean_inc_ref(v_type_3667_);
v_value_3668_ = lean_ctor_get(v_decl_3664_, 4);
lean_inc_ref(v_value_3668_);
v___x_3669_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3669_, 0, v_value_3668_);
v___x_3670_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3669_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3691_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3691_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3691_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
uint8_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = 0;
v___x_3676_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3675_, v_decl_3664_, v_type_3667_, v_params_3666_, v_a_3671_, v_a_3655_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
if (v_isShared_3674_ == 0)
{
lean_ctor_set_tag(v___x_3673_, 1);
lean_ctor_set(v___x_3673_, 0, v_a_3677_);
v___x_3679_ = v___x_3673_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3677_);
v___x_3679_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3680_, 0, v_k_3665_);
v___x_3681_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3679_, v___x_3680_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
return v___x_3681_;
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_del_object(v___x_3673_);
lean_dec_ref(v_k_3665_);
v_a_3683_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3676_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3676_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3667_);
lean_dec_ref(v_params_3666_);
lean_dec_ref(v_k_3665_);
lean_dec_ref(v_decl_3664_);
return v___x_3670_;
}
}
case 2:
{
lean_object* v_decl_3692_; lean_object* v_k_3693_; lean_object* v_params_3694_; lean_object* v_type_3695_; lean_object* v_value_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_decl_3692_ = lean_ctor_get(v_code_3652_, 0);
lean_inc_ref(v_decl_3692_);
v_k_3693_ = lean_ctor_get(v_code_3652_, 1);
lean_inc_ref(v_k_3693_);
lean_dec_ref_known(v_code_3652_, 2);
v_params_3694_ = lean_ctor_get(v_decl_3692_, 2);
lean_inc_ref(v_params_3694_);
v_type_3695_ = lean_ctor_get(v_decl_3692_, 3);
lean_inc_ref(v_type_3695_);
v_value_3696_ = lean_ctor_get(v_decl_3692_, 4);
lean_inc_ref(v_value_3696_);
v___x_3697_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3697_, 0, v_value_3696_);
v___x_3698_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3697_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3719_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3719_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3719_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
uint8_t v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = 0;
v___x_3704_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3703_, v_decl_3692_, v_type_3695_, v_params_3694_, v_a_3699_, v_a_3655_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3707_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
if (v_isShared_3702_ == 0)
{
lean_ctor_set_tag(v___x_3701_, 2);
lean_ctor_set(v___x_3701_, 0, v_a_3705_);
v___x_3707_ = v___x_3701_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3705_);
v___x_3707_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3708_, 0, v_k_3693_);
v___x_3709_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3707_, v___x_3708_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
return v___x_3709_;
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_del_object(v___x_3701_);
lean_dec_ref(v_k_3693_);
v_a_3711_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3704_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3704_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3695_);
lean_dec_ref(v_params_3694_);
lean_dec_ref(v_k_3693_);
lean_dec_ref(v_decl_3692_);
return v___x_3698_;
}
}
case 4:
{
lean_object* v_cases_3720_; lean_object* v___x_3721_; 
v_cases_3720_ = lean_ctor_get(v_code_3652_, 0);
lean_inc_ref_n(v_cases_3720_, 2);
v___x_3721_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3720_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3723_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3720_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_a_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_st_mk_ref(v___x_3724_);
v___x_3726_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3725_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3727_; lean_object* v_typeName_3728_; lean_object* v_resultType_3729_; lean_object* v_discr_3730_; lean_object* v_alts_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref_known(v___x_3726_, 1);
v___x_3727_ = lean_st_ref_get(v___x_3725_);
lean_dec(v___x_3725_);
v_typeName_3728_ = lean_ctor_get(v_cases_3720_, 0);
v_resultType_3729_ = lean_ctor_get(v_cases_3720_, 1);
v_discr_3730_ = lean_ctor_get(v_cases_3720_, 2);
v_alts_3731_ = lean_ctor_get(v_cases_3720_, 3);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_cases_3720_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3733_ = v_cases_3720_;
v_isShared_3734_ = v_isSharedCheck_3774_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_alts_3731_);
lean_inc(v_discr_3730_);
lean_inc(v_resultType_3729_);
lean_inc(v_typeName_3728_);
lean_dec(v_cases_3720_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3774_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_newArms_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_newArms_3735_ = lean_ctor_get(v___x_3727_, 1);
lean_inc_ref(v_newArms_3735_);
lean_dec(v___x_3727_);
v___x_3736_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3731_);
v___x_3737_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3735_, v___x_3736_, v_alts_3731_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3765_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3740_ = v___x_3737_;
v_isShared_3741_ = v_isSharedCheck_3765_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3765_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
uint8_t v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___y_3746_; uint8_t v___y_3758_; size_t v___x_3760_; size_t v___x_3761_; uint8_t v___x_3762_; 
v___x_3742_ = 0;
v___x_3743_ = lean_box(2);
v___x_3744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3735_, v___x_3743_);
lean_dec_ref(v_newArms_3735_);
v___x_3760_ = lean_ptr_addr(v_alts_3731_);
lean_dec_ref(v_alts_3731_);
v___x_3761_ = lean_ptr_addr(v_a_3738_);
v___x_3762_ = lean_usize_dec_eq(v___x_3760_, v___x_3761_);
if (v___x_3762_ == 0)
{
v___y_3758_ = v___x_3762_;
goto v___jp_3757_;
}
else
{
size_t v___x_3763_; uint8_t v___x_3764_; 
v___x_3763_ = lean_ptr_addr(v_resultType_3729_);
v___x_3764_ = lean_usize_dec_eq(v___x_3763_, v___x_3763_);
v___y_3758_ = v___x_3764_;
goto v___jp_3757_;
}
v___jp_3745_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
v___x_3747_ = lean_array_mk(v___x_3744_);
v___x_3748_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3742_, v___x_3747_, v___y_3746_);
lean_dec_ref(v___x_3747_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3748_);
v___x_3750_ = v___x_3740_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
v___jp_3752_:
{
lean_object* v___x_3754_; 
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 3, v_a_3738_);
v___x_3754_ = v___x_3733_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_typeName_3728_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_resultType_3729_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_discr_3730_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_a_3738_);
v___x_3754_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
v___y_3746_ = v___x_3755_;
goto v___jp_3745_;
}
}
v___jp_3757_:
{
if (v___y_3758_ == 0)
{
lean_dec_ref_known(v_code_3652_, 1);
goto v___jp_3752_;
}
else
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Lean_instBEqFVarId_beq(v_discr_3730_, v_discr_3730_);
if (v___x_3759_ == 0)
{
lean_dec_ref_known(v_code_3652_, 1);
goto v___jp_3752_;
}
else
{
lean_dec(v_a_3738_);
lean_del_object(v___x_3733_);
lean_dec(v_discr_3730_);
lean_dec_ref(v_resultType_3729_);
lean_dec(v_typeName_3728_);
v___y_3746_ = v_code_3652_;
goto v___jp_3745_;
}
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v_newArms_3735_);
lean_del_object(v___x_3733_);
lean_dec_ref(v_alts_3731_);
lean_dec(v_discr_3730_);
lean_dec_ref(v_resultType_3729_);
lean_dec(v_typeName_3728_);
lean_dec_ref_known(v_code_3652_, 1);
v_a_3766_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3737_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3737_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec(v___x_3725_);
lean_dec_ref(v_cases_3720_);
lean_dec_ref_known(v_code_3652_, 1);
v_a_3775_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3726_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3726_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_cases_3720_);
lean_dec_ref_known(v_code_3652_, 1);
v_a_3783_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3721_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3721_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
default: 
{
uint8_t v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3791_ = 0;
lean_inc(v_a_3653_);
v___x_3792_ = lean_array_mk(v_a_3653_);
v___x_3793_ = l_Array_reverse___redArg(v___x_3792_);
v___x_3794_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3791_, v___x_3793_, v_code_3652_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
return v___x_3795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3804_, lean_object* v_i_3805_, lean_object* v_as_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3813_ = lean_array_get_size(v_as_3806_);
v___x_3814_ = lean_nat_dec_lt(v_i_3805_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v_i_3805_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_as_3806_);
return v___x_3815_;
}
else
{
lean_object* v_options_3816_; lean_object* v_inheritedTraceOptions_3817_; uint8_t v_hasTrace_3818_; uint8_t v___x_3819_; lean_object* v_a_3820_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; 
v_options_3816_ = lean_ctor_get(v___y_3810_, 2);
v_inheritedTraceOptions_3817_ = lean_ctor_get(v___y_3810_, 13);
v_hasTrace_3818_ = lean_ctor_get_uint8(v_options_3816_, sizeof(void*)*1);
v___x_3819_ = 0;
v_a_3820_ = lean_array_fget_borrowed(v_as_3806_, v_i_3805_);
v___x_3851_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3820_);
v___x_3852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3804_, v___x_3851_);
if (v_hasTrace_3818_ == 0)
{
lean_dec(v___x_3851_);
v___y_3854_ = v___y_3808_;
v___y_3855_ = v___y_3809_;
v___y_3856_ = v___y_3810_;
v___y_3857_ = v___y_3811_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3862_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3863_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3817_, v_options_3816_, v___x_3863_);
if (v___x_3864_ == 0)
{
lean_dec(v___x_3851_);
v___y_3854_ = v___y_3808_;
v___y_3855_ = v___y_3809_;
v___y_3856_ = v___y_3810_;
v___y_3857_ = v___y_3811_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3865_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3866_ = lean_unsigned_to_nat(0u);
v___x_3867_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3851_, v___x_3866_);
v___x_3868_ = l_Lean_MessageData_ofFormat(v___x_3867_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3865_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3869_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_List_lengthTR___redArg(v___x_3852_);
v___x_3873_ = l_Nat_reprFast(v___x_3872_);
v___x_3874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = l_Lean_MessageData_ofFormat(v___x_3874_);
v___x_3876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3871_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v___x_3877_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3862_, v___x_3876_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_dec_ref_known(v___x_3877_, 1);
v___y_3854_ = v___y_3808_;
v___y_3855_ = v___y_3809_;
v___y_3856_ = v___y_3810_;
v___y_3857_ = v___y_3811_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v___x_3852_);
lean_dec_ref(v_as_3806_);
lean_dec(v_i_3805_);
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
v___jp_3821_:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3828_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3819_, v___y_3825_, v___y_3827_);
lean_dec_ref(v___y_3825_);
v___x_3829_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3829_, 0, v___x_3828_);
v___x_3830_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3829_, v___y_3826_, v___y_3823_, v___y_3824_, v___y_3822_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; size_t v___x_3833_; size_t v___x_3834_; uint8_t v___x_3835_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
lean_inc(v_a_3820_);
v___x_3832_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3820_, v_a_3831_);
v___x_3833_ = lean_ptr_addr(v_a_3820_);
v___x_3834_ = lean_ptr_addr(v___x_3832_);
v___x_3835_ = lean_usize_dec_eq(v___x_3833_, v___x_3834_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_unsigned_to_nat(1u);
v___x_3837_ = lean_nat_add(v_i_3805_, v___x_3836_);
v___x_3838_ = lean_array_fset(v_as_3806_, v_i_3805_, v___x_3832_);
lean_dec(v_i_3805_);
v_i_3805_ = v___x_3837_;
v_as_3806_ = v___x_3838_;
goto _start;
}
else
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec_ref(v___x_3832_);
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_nat_add(v_i_3805_, v___x_3840_);
lean_dec(v_i_3805_);
v_i_3805_ = v___x_3841_;
goto _start;
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref(v_as_3806_);
lean_dec(v_i_3805_);
v_a_3843_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3830_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3830_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
v___jp_3853_:
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_array_mk(v___x_3852_);
switch(lean_obj_tag(v_a_3820_))
{
case 0:
{
lean_object* v_code_3859_; 
v_code_3859_ = lean_ctor_get(v_a_3820_, 2);
lean_inc_ref(v_code_3859_);
v___y_3822_ = v___y_3857_;
v___y_3823_ = v___y_3855_;
v___y_3824_ = v___y_3856_;
v___y_3825_ = v___x_3858_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v_code_3859_;
goto v___jp_3821_;
}
case 1:
{
lean_object* v_code_3860_; 
v_code_3860_ = lean_ctor_get(v_a_3820_, 1);
lean_inc_ref(v_code_3860_);
v___y_3822_ = v___y_3857_;
v___y_3823_ = v___y_3855_;
v___y_3824_ = v___y_3856_;
v___y_3825_ = v___x_3858_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v_code_3860_;
goto v___jp_3821_;
}
default: 
{
lean_object* v_code_3861_; 
v_code_3861_ = lean_ctor_get(v_a_3820_, 0);
lean_inc_ref(v_code_3861_);
v___y_3822_ = v___y_3857_;
v___y_3823_ = v___y_3855_;
v___y_3824_ = v___y_3856_;
v___y_3825_ = v___x_3858_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v_code_3861_;
goto v___jp_3821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3886_, lean_object* v_i_3887_, lean_object* v_as_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3886_, v_i_3887_, v_as_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___x_3886_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3896_, lean_object* v_v_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
if (lean_obj_tag(v_v_3897_) == 0)
{
lean_object* v_code_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3928_; 
v_code_3904_ = lean_ctor_get(v_v_3897_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_v_3897_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3906_ = v_v_3897_;
v_isShared_3907_ = v_isSharedCheck_3928_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_code_3904_);
lean_dec(v_v_3897_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3928_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; 
lean_inc(v___y_3902_);
lean_inc_ref(v___y_3901_);
lean_inc(v___y_3900_);
lean_inc_ref(v___y_3899_);
lean_inc(v___y_3898_);
v___x_3908_ = lean_apply_7(v_f_3896_, v_code_3904_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, lean_box(0));
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3919_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_3919_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3919_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_a_3909_);
v___x_3914_ = v___x_3906_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_3914_);
v___x_3916_ = v___x_3911_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_del_object(v___x_3906_);
v_a_3920_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3908_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3908_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
else
{
lean_object* v___x_3929_; 
lean_dec_ref(v_f_3896_);
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_v_3897_);
return v___x_3929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3930_, lean_object* v_v_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3930_, v_v_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3939_, lean_object* v_f_3940_, lean_object* v_v_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3940_, v_v_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3949_, lean_object* v_f_3950_, lean_object* v_v_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v_pu_boxed_3958_; lean_object* v_res_3959_; 
v_pu_boxed_3958_ = lean_unbox(v_pu_3949_);
v_res_3959_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_3958_, v_f_3950_, v_v_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_toSignature_3967_; lean_object* v_value_3968_; uint8_t v_recursive_3969_; lean_object* v_inlineAttr_x3f_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3996_; 
v_toSignature_3967_ = lean_ctor_get(v_decl_3961_, 0);
v_value_3968_ = lean_ctor_get(v_decl_3961_, 1);
v_recursive_3969_ = lean_ctor_get_uint8(v_decl_3961_, sizeof(void*)*3);
v_inlineAttr_x3f_3970_ = lean_ctor_get(v_decl_3961_, 2);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_decl_3961_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3972_ = v_decl_3961_;
v_isShared_3973_ = v_isSharedCheck_3996_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_inlineAttr_x3f_3970_);
lean_inc(v_value_3968_);
lean_inc(v_toSignature_3967_);
lean_dec(v_decl_3961_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3996_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_3975_ = lean_box(0);
v___x_3976_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_3974_, v_value_3968_, v___x_3975_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3987_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3987_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3987_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v_a_3977_);
v___x_3982_ = v___x_3972_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_toSignature_3967_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_a_3977_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_inlineAttr_x3f_3970_);
lean_ctor_set_uint8(v_reuseFailAlloc_3986_, sizeof(void*)*3, v_recursive_3969_);
v___x_3982_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3984_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_3982_);
v___x_3984_ = v___x_3979_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_del_object(v___x_3972_);
lean_dec(v_inlineAttr_x3f_3970_);
lean_dec_ref(v_toSignature_3967_);
v_a_3988_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3976_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3976_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_4020_, lean_object* v___f_4021_, lean_object* v_occurrence_4022_, lean_object* v_h_4023_){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_4025_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_4024_, v_phase_4020_, v___f_4021_, v_occurrence_4022_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_4026_, lean_object* v___f_4027_, lean_object* v_occurrence_4028_, lean_object* v_h_4029_){
_start:
{
uint8_t v_phase_boxed_4030_; lean_object* v_res_4031_; 
v_phase_boxed_4030_ = lean_unbox(v_phase_4026_);
v_res_4031_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_4030_, v___f_4027_, v_occurrence_4028_, v_h_4029_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_4033_, lean_object* v_occurrence_4034_){
_start:
{
lean_object* v___f_4035_; lean_object* v___x_4036_; lean_object* v___f_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; 
v___f_4035_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_4036_ = lean_box(v_phase_4033_);
v___f_4037_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4037_, 0, v___x_4036_);
lean_closure_set(v___f_4037_, 1, v___f_4035_);
lean_closure_set(v___f_4037_, 2, v_occurrence_4034_);
v___x_4038_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_4039_ = 0;
v___x_4040_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_4038_, v_phase_4033_, v___x_4039_, v___f_4037_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_4041_, lean_object* v_occurrence_4042_){
_start:
{
uint8_t v_phase_boxed_4043_; lean_object* v_res_4044_; 
v_phase_boxed_4043_ = lean_unbox(v_phase_4041_);
v_res_4044_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_4043_, v_occurrence_4042_);
return v_res_4044_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = lean_unsigned_to_nat(3411573818u);
v___x_4097_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4098_ = l_Lean_Name_num___override(v___x_4097_, v___x_4096_);
return v___x_4098_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4101_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4102_ = l_Lean_Name_str___override(v___x_4101_, v___x_4100_);
return v___x_4102_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4105_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4106_ = l_Lean_Name_str___override(v___x_4105_, v___x_4104_);
return v___x_4106_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = lean_unsigned_to_nat(2u);
v___x_4108_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4109_ = l_Lean_Name_num___override(v___x_4108_, v___x_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4111_; uint8_t v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4111_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4112_ = 1;
v___x_4113_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4114_ = l_Lean_registerTraceClass(v___x_4111_, v___x_4112_, v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4116_;
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
