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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1;
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
lean_dec_ref(v_t_8_);
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
lean_object* v___x_56_; uint64_t v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1723u);
v___x_57_ = lean_uint64_of_nat(v___x_56_);
return v___x_57_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1(void){
_start:
{
uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; 
v___x_58_ = lean_uint64_once(&l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0);
v___x_59_ = 0ULL;
v___x_60_ = lean_uint64_mix_hash(v___x_59_, v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(lean_object* v_x_61_){
_start:
{
switch(lean_obj_tag(v_x_61_))
{
case 0:
{
lean_object* v_name_62_; uint64_t v___x_63_; 
v_name_62_ = lean_ctor_get(v_x_61_, 0);
v___x_63_ = 0ULL;
if (lean_obj_tag(v_name_62_) == 0)
{
uint64_t v___x_64_; 
v___x_64_ = lean_uint64_once(&l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1);
return v___x_64_;
}
else
{
uint64_t v_hash_65_; uint64_t v___x_66_; 
v_hash_65_ = lean_ctor_get_uint64(v_name_62_, sizeof(void*)*2);
v___x_66_ = lean_uint64_mix_hash(v___x_63_, v_hash_65_);
return v___x_66_;
}
}
case 1:
{
uint64_t v___x_67_; 
v___x_67_ = 1ULL;
return v___x_67_;
}
case 2:
{
uint64_t v___x_68_; 
v___x_68_ = 2ULL;
return v___x_68_;
}
default: 
{
uint64_t v___x_69_; 
v___x_69_ = 3ULL;
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed(lean_object* v_x_70_){
_start:
{
uint64_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_x_70_);
lean_dec(v_x_70_);
v_r_72_ = lean_box_uint64(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_name_77_; lean_object* v_name_78_; uint8_t v___x_79_; 
v_name_77_ = lean_ctor_get(v_x_75_, 0);
v_name_78_ = lean_ctor_get(v_x_76_, 0);
v___x_79_ = lean_name_eq(v_name_77_, v_name_78_);
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
case 1:
{
if (lean_obj_tag(v_x_76_) == 1)
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
case 2:
{
if (lean_obj_tag(v_x_76_) == 2)
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
default: 
{
if (lean_obj_tag(v_x_76_) == 3)
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_x_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(2u);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_to_int(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(lean_object* v_x_116_, lean_object* v_prec_117_){
_start:
{
lean_object* v___y_119_; lean_object* v___y_126_; lean_object* v___y_133_; 
switch(lean_obj_tag(v_x_116_))
{
case 0:
{
lean_object* v_name_139_; lean_object* v___y_141_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_name_139_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_name_139_);
lean_dec_ref(v_x_116_);
v___x_150_ = lean_unsigned_to_nat(1024u);
v___x_151_ = lean_nat_dec_le(v___x_150_, v_prec_117_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_141_ = v___x_152_;
goto v___jp_140_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_141_ = v___x_153_;
goto v___jp_140_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_142_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8));
v___x_143_ = lean_unsigned_to_nat(1024u);
v___x_144_ = l_Lean_Name_reprPrec(v_name_139_, v___x_143_);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_142_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
lean_inc(v___y_141_);
v___x_146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_146_, 0, v___y_141_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = 0;
v___x_148_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_147_);
v___x_149_ = l_Repr_addAppParen(v___x_148_, v_prec_117_);
return v___x_149_;
}
}
case 1:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1024u);
v___x_155_ = lean_nat_dec_le(v___x_154_, v_prec_117_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_119_ = v___x_156_;
goto v___jp_118_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_119_ = v___x_157_;
goto v___jp_118_;
}
}
case 2:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(1024u);
v___x_159_ = lean_nat_dec_le(v___x_158_, v_prec_117_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_126_ = v___x_160_;
goto v___jp_125_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_126_ = v___x_161_;
goto v___jp_125_;
}
}
default: 
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1024u);
v___x_163_ = lean_nat_dec_le(v___x_162_, v_prec_117_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_133_ = v___x_164_;
goto v___jp_132_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_133_ = v___x_165_;
goto v___jp_132_;
}
}
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1));
lean_inc(v___y_119_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___y_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = 0;
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = l_Repr_addAppParen(v___x_123_, v_prec_117_);
return v___x_124_;
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_127_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3));
lean_inc(v___y_126_);
v___x_128_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_128_, 0, v___y_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = 0;
v___x_130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_129_);
v___x_131_ = l_Repr_addAppParen(v___x_130_, v_prec_117_);
return v___x_131_;
}
v___jp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5));
lean_inc(v___y_133_);
v___x_135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_135_, 0, v___y_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = 0;
v___x_137_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*1, v___x_136_);
v___x_138_ = l_Repr_addAppParen(v___x_137_, v_prec_117_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed(lean_object* v_x_166_, lean_object* v_prec_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v_x_166_, v_prec_167_);
lean_dec(v_prec_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v_ctorName_172_; lean_object* v___x_173_; 
v_ctorName_172_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_ctorName_172_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_ctorName_172_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(1);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_x_175_);
lean_dec_ref(v_x_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object* v_decl_177_, lean_object* v_x_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc(v_a_179_);
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v_decl_177_);
lean_ctor_set(v___x_185_, 1, v_a_179_);
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
v___x_186_ = lean_apply_6(v_x_178_, v___x_185_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, lean_box(0));
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg___boxed(lean_object* v_decl_187_, lean_object* v_x_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_187_, v_x_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* v_00_u03b1_196_, lean_object* v_decl_197_, lean_object* v_x_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_197_, v_x_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___boxed(lean_object* v_00_u03b1_206_, lean_object* v_decl_207_, lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(v_00_u03b1_206_, v_decl_207_, v_x_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(0);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
v___x_223_ = lean_apply_6(v_x_216_, v___x_222_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg___boxed(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* v_00_u03b1_231_, lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_232_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object* v_00_u03b1_240_, lean_object* v_x_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(v_00_u03b1_240_, v_x_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object* v_decl_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_type_255_; lean_object* v_value_256_; lean_object* v___x_257_; 
v_type_255_ = lean_ctor_get(v_decl_249_, 2);
lean_inc_ref(v_type_255_);
v_value_256_ = lean_ctor_get(v_decl_249_, 3);
lean_inc(v_value_256_);
lean_dec_ref(v_decl_249_);
v___x_257_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_255_, v_a_253_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_306_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_306_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_306_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_306_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
if (lean_obj_tag(v_a_258_) == 0)
{
uint8_t v___x_262_; 
v___x_262_ = 0;
if (lean_obj_tag(v_value_256_) == 2)
{
lean_object* v_struct_263_; lean_object* v___x_264_; 
lean_del_object(v___x_260_);
v_struct_263_ = lean_ctor_get(v_value_256_, 2);
lean_inc(v_struct_263_);
lean_dec_ref(v_value_256_);
v___x_264_ = l_Lean_Compiler_LCNF_getType(v_struct_263_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_264_);
v___x_266_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_a_265_, v_a_253_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_280_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_280_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_280_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
if (lean_obj_tag(v_a_267_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = lean_box(v___x_262_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec_ref(v_a_267_);
v___x_275_ = 1;
v___x_276_ = lean_box(v___x_275_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_276_);
v___x_278_ = v___x_269_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
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
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_266_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_266_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_264_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_264_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec(v_value_256_);
v___x_297_ = lean_box(v___x_262_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_297_);
v___x_299_ = v___x_260_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_dec_ref(v_a_258_);
lean_dec(v_value_256_);
v___x_301_ = 1;
v___x_302_ = lean_box(v___x_301_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_302_);
v___x_304_ = v___x_260_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v_value_256_);
v_a_307_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_257_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_257_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object* v_decl_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* v_decl_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_322_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object* v_decl_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(v_decl_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
return v_res_337_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object* v_a_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
else
{
lean_object* v_key_341_; lean_object* v_tail_342_; uint8_t v___x_343_; 
v_key_341_ = lean_ctor_get(v_x_339_, 0);
v_tail_342_ = lean_ctor_get(v_x_339_, 2);
v___x_343_ = l_Lean_instBEqFVarId_beq(v_key_341_, v_a_338_);
if (v___x_343_ == 0)
{
v_x_339_ = v_tail_342_;
goto _start;
}
else
{
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object* v_a_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_345_, v_x_346_);
lean_dec(v_x_346_);
lean_dec(v_a_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_buckets_351_; lean_object* v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v_fold_356_; uint64_t v___x_357_; uint64_t v___x_358_; uint64_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_buckets_351_ = lean_ctor_get(v_m_349_, 1);
v___x_352_ = lean_array_get_size(v_buckets_351_);
v___x_353_ = l_Lean_instHashableFVarId_hash(v_a_350_);
v___x_354_ = 32ULL;
v___x_355_ = lean_uint64_shift_right(v___x_353_, v___x_354_);
v_fold_356_ = lean_uint64_xor(v___x_353_, v___x_355_);
v___x_357_ = 16ULL;
v___x_358_ = lean_uint64_shift_right(v_fold_356_, v___x_357_);
v___x_359_ = lean_uint64_xor(v_fold_356_, v___x_358_);
v___x_360_ = lean_uint64_to_usize(v___x_359_);
v___x_361_ = lean_usize_of_nat(v___x_352_);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_sub(v___x_361_, v___x_362_);
v___x_364_ = lean_usize_land(v___x_360_, v___x_363_);
v___x_365_ = lean_array_uget_borrowed(v_buckets_351_, v___x_364_);
v___x_366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_350_, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object* v_m_367_, lean_object* v_a_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_m_367_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
return v_x_371_;
}
else
{
lean_object* v_key_373_; lean_object* v_value_374_; lean_object* v_tail_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_398_; 
v_key_373_ = lean_ctor_get(v_x_372_, 0);
v_value_374_ = lean_ctor_get(v_x_372_, 1);
v_tail_375_ = lean_ctor_get(v_x_372_, 2);
v_isSharedCheck_398_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_398_ == 0)
{
v___x_377_ = v_x_372_;
v_isShared_378_ = v_isSharedCheck_398_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_tail_375_);
lean_inc(v_value_374_);
lean_inc(v_key_373_);
lean_dec(v_x_372_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_398_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v___x_382_; uint64_t v_fold_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_379_ = lean_array_get_size(v_x_371_);
v___x_380_ = l_Lean_instHashableFVarId_hash(v_key_373_);
v___x_381_ = 32ULL;
v___x_382_ = lean_uint64_shift_right(v___x_380_, v___x_381_);
v_fold_383_ = lean_uint64_xor(v___x_380_, v___x_382_);
v___x_384_ = 16ULL;
v___x_385_ = lean_uint64_shift_right(v_fold_383_, v___x_384_);
v___x_386_ = lean_uint64_xor(v_fold_383_, v___x_385_);
v___x_387_ = lean_uint64_to_usize(v___x_386_);
v___x_388_ = lean_usize_of_nat(v___x_379_);
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_sub(v___x_388_, v___x_389_);
v___x_391_ = lean_usize_land(v___x_387_, v___x_390_);
v___x_392_ = lean_array_uget_borrowed(v_x_371_, v___x_391_);
lean_inc(v___x_392_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 2, v___x_392_);
v___x_394_ = v___x_377_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_key_373_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_value_374_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v___x_392_);
v___x_394_ = v_reuseFailAlloc_397_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_array_uset(v_x_371_, v___x_391_, v___x_394_);
v_x_371_ = v___x_395_;
v_x_372_ = v_tail_375_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(lean_object* v_i_399_, lean_object* v_source_400_, lean_object* v_target_401_){
_start:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_array_get_size(v_source_400_);
v___x_403_ = lean_nat_dec_lt(v_i_399_, v___x_402_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_source_400_);
lean_dec(v_i_399_);
return v_target_401_;
}
else
{
lean_object* v_es_404_; lean_object* v___x_405_; lean_object* v_source_406_; lean_object* v_target_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_es_404_ = lean_array_fget(v_source_400_, v_i_399_);
v___x_405_ = lean_box(0);
v_source_406_ = lean_array_fset(v_source_400_, v_i_399_, v___x_405_);
v_target_407_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_target_401_, v_es_404_);
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_add(v_i_399_, v___x_408_);
lean_dec(v_i_399_);
v_i_399_ = v___x_409_;
v_source_400_ = v_source_406_;
v_target_401_ = v_target_407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object* v_data_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_nbuckets_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_412_ = lean_array_get_size(v_data_411_);
v___x_413_ = lean_unsigned_to_nat(2u);
v_nbuckets_414_ = lean_nat_mul(v___x_412_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_box(0);
v___x_417_ = lean_mk_array(v_nbuckets_414_, v___x_416_);
v___x_418_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v___x_415_, v_data_411_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object* v_m_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
lean_object* v_size_422_; lean_object* v_buckets_423_; lean_object* v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v_fold_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v_bkt_437_; uint8_t v___x_438_; 
v_size_422_ = lean_ctor_get(v_m_419_, 0);
v_buckets_423_ = lean_ctor_get(v_m_419_, 1);
v___x_424_ = lean_array_get_size(v_buckets_423_);
v___x_425_ = l_Lean_instHashableFVarId_hash(v_a_420_);
v___x_426_ = 32ULL;
v___x_427_ = lean_uint64_shift_right(v___x_425_, v___x_426_);
v_fold_428_ = lean_uint64_xor(v___x_425_, v___x_427_);
v___x_429_ = 16ULL;
v___x_430_ = lean_uint64_shift_right(v_fold_428_, v___x_429_);
v___x_431_ = lean_uint64_xor(v_fold_428_, v___x_430_);
v___x_432_ = lean_uint64_to_usize(v___x_431_);
v___x_433_ = lean_usize_of_nat(v___x_424_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v___x_433_, v___x_434_);
v___x_436_ = lean_usize_land(v___x_432_, v___x_435_);
v_bkt_437_ = lean_array_uget_borrowed(v_buckets_423_, v___x_436_);
v___x_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_420_, v_bkt_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_459_; 
lean_inc_ref(v_buckets_423_);
lean_inc(v_size_422_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_m_419_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_460_ = lean_ctor_get(v_m_419_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_m_419_, 0);
lean_dec(v_unused_461_);
v___x_440_ = v_m_419_;
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_m_419_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_size_x27_443_; lean_object* v___x_444_; lean_object* v_buckets_x27_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_442_ = lean_unsigned_to_nat(1u);
v_size_x27_443_ = lean_nat_add(v_size_422_, v___x_442_);
lean_dec(v_size_422_);
lean_inc(v_bkt_437_);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v_a_420_);
lean_ctor_set(v___x_444_, 1, v_b_421_);
lean_ctor_set(v___x_444_, 2, v_bkt_437_);
v_buckets_x27_445_ = lean_array_uset(v_buckets_423_, v___x_436_, v___x_444_);
v___x_446_ = lean_unsigned_to_nat(4u);
v___x_447_ = lean_nat_mul(v_size_x27_443_, v___x_446_);
v___x_448_ = lean_unsigned_to_nat(3u);
v___x_449_ = lean_nat_div(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_array_get_size(v_buckets_x27_445_);
v___x_451_ = lean_nat_dec_le(v___x_449_, v___x_450_);
lean_dec(v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v_val_452_; lean_object* v___x_454_; 
v_val_452_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_445_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_val_452_);
lean_ctor_set(v___x_440_, 0, v_size_x27_443_);
v___x_454_ = v___x_440_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_size_x27_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_val_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_buckets_x27_445_);
lean_ctor_set(v___x_440_, 0, v_size_x27_443_);
v___x_457_ = v___x_440_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_size_x27_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_buckets_x27_445_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_dec(v_b_421_);
lean_dec(v_a_420_);
return v_m_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object* v_var_462_, uint8_t v_borrowed_463_, lean_object* v_a_464_){
_start:
{
if (lean_obj_tag(v_var_462_) == 1)
{
lean_object* v_fvarId_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_484_; 
v_fvarId_466_ = lean_ctor_get(v_var_462_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_var_462_);
if (v_isSharedCheck_484_ == 0)
{
v___x_468_ = v_var_462_;
v_isShared_469_ = v_isSharedCheck_484_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_fvarId_466_);
lean_dec(v_var_462_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_484_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_st_ref_get(v_a_464_);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_470_, v_fvarId_466_);
lean_dec(v___x_470_);
if (v_borrowed_463_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_472_ = lean_st_ref_take(v_a_464_);
v___x_473_ = lean_box(0);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_472_, v_fvarId_466_, v___x_473_);
v___x_475_ = lean_st_ref_set(v_a_464_, v___x_474_);
v___x_476_ = lean_box(v___x_471_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 0);
lean_ctor_set(v___x_468_, 0, v___x_476_);
v___x_478_ = v___x_468_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_fvarId_466_);
v___x_480_ = lean_box(v___x_471_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 0);
lean_ctor_set(v___x_468_, 0, v___x_480_);
v___x_482_ = v___x_468_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_var_462_);
v___x_485_ = 0;
v___x_486_ = lean_box(v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object* v_var_488_, lean_object* v_borrowed_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
uint8_t v_borrowed_boxed_492_; lean_object* v_res_493_; 
v_borrowed_boxed_492_ = lean_unbox(v_borrowed_489_);
v_res_493_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_488_, v_borrowed_boxed_492_, v_a_490_);
lean_dec(v_a_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object* v_var_494_, uint8_t v_borrowed_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_494_, v_borrowed_495_, v_a_496_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object* v_var_503_, lean_object* v_borrowed_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
uint8_t v_borrowed_boxed_511_; lean_object* v_res_512_; 
v_borrowed_boxed_511_ = lean_unbox(v_borrowed_504_);
v_res_512_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_503_, v_borrowed_boxed_511_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
return v_res_512_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object* v_00_u03b2_513_, lean_object* v_m_514_, lean_object* v_a_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_514_, v_a_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object* v_00_u03b2_517_, lean_object* v_m_518_, lean_object* v_a_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_517_, v_m_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_m_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_523_, v_a_524_, v_b_525_);
return v___x_526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_531_, lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_531_, v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec(v_a_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object* v_00_u03b2_536_, lean_object* v_data_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_data_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_539_, lean_object* v_i_540_, lean_object* v_source_541_, lean_object* v_target_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v_i_540_, v_source_541_, v_target_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_x_545_, v_x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object* v_as_548_, size_t v_i_549_, size_t v_stop_550_, uint8_t v_b_551_, lean_object* v___y_552_){
_start:
{
uint8_t v_a_555_; lean_object* v___y_560_; uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_eq(v_i_549_, v_stop_550_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_array_uget_borrowed(v_as_548_, v_i_549_);
lean_inc(v___x_564_);
v___x_565_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_564_, v___x_563_, v___y_552_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; uint8_t v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
v___x_567_ = lean_unbox(v_a_566_);
lean_dec(v_a_566_);
if (v___x_567_ == 0)
{
lean_dec_ref(v___x_565_);
v_a_555_ = v_b_551_;
goto v___jp_554_;
}
else
{
v___y_560_ = v___x_565_;
goto v___jp_559_;
}
}
else
{
v___y_560_ = v___x_565_;
goto v___jp_559_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(v_b_551_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
v___jp_554_:
{
size_t v___x_556_; size_t v___x_557_; 
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_549_, v___x_556_);
v_i_549_ = v___x_557_;
v_b_551_ = v_a_555_;
goto _start;
}
v___jp_559_:
{
if (lean_obj_tag(v___y_560_) == 0)
{
lean_object* v_a_561_; uint8_t v___x_562_; 
v_a_561_ = lean_ctor_get(v___y_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v___y_560_);
v___x_562_ = lean_unbox(v_a_561_);
lean_dec(v_a_561_);
v_a_555_ = v___x_562_;
goto v___jp_554_;
}
else
{
return v___y_560_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_570_, lean_object* v_i_571_, lean_object* v_stop_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
size_t v_i_boxed_576_; size_t v_stop_boxed_577_; uint8_t v_b_boxed_578_; lean_object* v_res_579_; 
v_i_boxed_576_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_stop_boxed_577_ = lean_unbox_usize(v_stop_572_);
lean_dec(v_stop_572_);
v_b_boxed_578_ = lean_unbox(v_b_573_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_570_, v_i_boxed_576_, v_stop_boxed_577_, v_b_boxed_578_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v_as_570_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_580_, lean_object* v_args_581_, lean_object* v_val_582_, lean_object* v_a_583_, uint8_t v_b_584_, lean_object* v___y_585_){
_start:
{
uint8_t v_a_588_; uint8_t v___x_592_; 
v___x_592_ = lean_nat_dec_lt(v_a_583_, v_upperBound_580_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_a_583_);
v___x_593_ = lean_box(v_b_584_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
else
{
lean_object* v_params_595_; lean_object* v___x_596_; uint8_t v___y_598_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_params_595_ = lean_ctor_get(v_val_582_, 3);
v___x_596_ = lean_array_fget_borrowed(v_args_581_, v_a_583_);
v___x_603_ = lean_array_get_size(v_params_595_);
v___x_604_ = lean_nat_dec_lt(v_a_583_, v___x_603_);
if (v___x_604_ == 0)
{
v___y_598_ = v___x_604_;
goto v___jp_597_;
}
else
{
lean_object* v___x_605_; uint8_t v_borrow_606_; 
v___x_605_ = lean_array_fget_borrowed(v_params_595_, v_a_583_);
v_borrow_606_ = lean_ctor_get_uint8(v___x_605_, sizeof(void*)*3);
v___y_598_ = v_borrow_606_;
goto v___jp_597_;
}
v___jp_597_:
{
lean_object* v___x_599_; 
lean_inc(v___x_596_);
v___x_599_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_596_, v___y_598_, v___y_585_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; uint8_t v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_unbox(v_a_600_);
if (v___x_601_ == 0)
{
lean_dec(v_a_600_);
v_a_588_ = v_b_584_;
goto v___jp_587_;
}
else
{
uint8_t v___x_602_; 
v___x_602_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
v_a_588_ = v___x_602_;
goto v___jp_587_;
}
}
else
{
lean_dec(v_a_583_);
return v___x_599_;
}
}
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_a_583_, v___x_589_);
lean_dec(v_a_583_);
v_a_583_ = v___x_590_;
v_b_584_ = v_a_588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object* v_upperBound_607_, lean_object* v_args_608_, lean_object* v_val_609_, lean_object* v_a_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v_b_boxed_614_; lean_object* v_res_615_; 
v_b_boxed_614_ = lean_unbox(v_b_611_);
v_res_615_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_607_, v_args_608_, v_val_609_, v_a_610_, v_b_boxed_614_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v_val_609_);
lean_dec_ref(v_args_608_);
lean_dec(v_upperBound_607_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_, uint8_t v_b_619_, lean_object* v___y_620_){
_start:
{
uint8_t v_a_623_; lean_object* v___y_628_; uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_eq(v_i_617_, v_stop_618_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_array_uget_borrowed(v_as_616_, v_i_617_);
lean_inc(v___x_632_);
v___x_633_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_632_, v___x_631_, v___y_620_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; uint8_t v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
v___x_635_ = lean_unbox(v_a_634_);
lean_dec(v_a_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v___x_633_);
v_a_623_ = v_b_619_;
goto v___jp_622_;
}
else
{
v___y_628_ = v___x_633_;
goto v___jp_627_;
}
}
else
{
v___y_628_ = v___x_633_;
goto v___jp_627_;
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(v_b_619_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
v___jp_622_:
{
size_t v___x_624_; size_t v___x_625_; 
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_617_, v___x_624_);
v_i_617_ = v___x_625_;
v_b_619_ = v_a_623_;
goto _start;
}
v___jp_627_:
{
if (lean_obj_tag(v___y_628_) == 0)
{
lean_object* v_a_629_; uint8_t v___x_630_; 
v_a_629_ = lean_ctor_get(v___y_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___y_628_);
v___x_630_ = lean_unbox(v_a_629_);
lean_dec(v_a_629_);
v_a_623_ = v___x_630_;
goto v___jp_622_;
}
else
{
return v___y_628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_638_, lean_object* v_i_639_, lean_object* v_stop_640_, lean_object* v_b_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
size_t v_i_boxed_644_; size_t v_stop_boxed_645_; uint8_t v_b_boxed_646_; lean_object* v_res_647_; 
v_i_boxed_644_ = lean_unbox_usize(v_i_639_);
lean_dec(v_i_639_);
v_stop_boxed_645_ = lean_unbox_usize(v_stop_640_);
lean_dec(v_stop_640_);
v_b_boxed_646_ = lean_unbox(v_b_641_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_638_, v_i_boxed_644_, v_stop_boxed_645_, v_b_boxed_646_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v_as_638_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object* v_value_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
switch(lean_obj_tag(v_value_648_))
{
case 0:
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_663_; 
v_isSharedCheck_663_ = !lean_is_exclusive(v_value_648_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_value_648_, 0);
lean_dec(v_unused_664_);
v___x_656_ = v_value_648_;
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_value_648_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = 0;
v___x_659_ = lean_box(v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
case 1:
{
uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = 0;
v___x_666_ = lean_box(v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
case 2:
{
lean_object* v_struct_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; 
v_struct_668_ = lean_ctor_get(v_value_648_, 2);
lean_inc(v_struct_668_);
lean_dec_ref(v_value_648_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_struct_668_);
v___x_670_ = 1;
v___x_671_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_669_, v___x_670_, v_a_649_);
return v___x_671_;
}
case 3:
{
lean_object* v_declName_672_; lean_object* v_args_673_; lean_object* v___x_674_; 
v_declName_672_ = lean_ctor_get(v_value_648_, 0);
lean_inc(v_declName_672_);
v_args_673_ = lean_ctor_get(v_value_648_, 2);
lean_inc_ref(v_args_673_);
lean_dec_ref(v_value_648_);
v___x_674_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_672_, v_a_653_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_703_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_703_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_703_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_703_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
if (lean_obj_tag(v_a_675_) == 0)
{
uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = 0;
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_args_673_);
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_685_; 
lean_dec_ref(v_args_673_);
v___x_683_ = lean_box(v___x_679_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_683_);
v___x_685_ = v___x_677_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
else
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_le(v___x_681_, v___x_681_);
if (v___x_687_ == 0)
{
if (v___x_682_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec_ref(v_args_673_);
v___x_688_ = lean_box(v___x_679_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_688_);
v___x_690_ = v___x_677_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
else
{
size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
lean_del_object(v___x_677_);
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_681_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_673_, v___x_692_, v___x_693_, v___x_679_, v_a_649_);
lean_dec_ref(v_args_673_);
return v___x_694_;
}
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
lean_del_object(v___x_677_);
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_681_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_673_, v___x_695_, v___x_696_, v___x_679_, v_a_649_);
lean_dec_ref(v_args_673_);
return v___x_697_;
}
}
}
else
{
lean_object* v_val_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; 
lean_del_object(v___x_677_);
v_val_698_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v_a_675_);
v___x_699_ = lean_array_get_size(v_args_673_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = 0;
v___x_702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_699_, v_args_673_, v_val_698_, v___x_700_, v___x_701_, v_a_649_);
lean_dec(v_val_698_);
lean_dec_ref(v_args_673_);
return v___x_702_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v_args_673_);
v_a_704_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_674_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_674_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
default: 
{
lean_object* v_fvarId_712_; lean_object* v_args_713_; lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_fvarId_712_ = lean_ctor_get(v_value_648_, 0);
lean_inc(v_fvarId_712_);
v_args_713_ = lean_ctor_get(v_value_648_, 1);
lean_inc_ref(v_args_713_);
lean_dec_ref(v_value_648_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_fvarId_712_);
v___x_715_ = 0;
v___x_716_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_714_, v___x_715_, v_a_649_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_array_get_size(v_args_713_);
v___x_720_ = lean_nat_dec_lt(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v_a_717_);
lean_dec_ref(v_args_713_);
return v___x_716_;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = lean_nat_dec_le(v___x_719_, v___x_719_);
if (v___x_721_ == 0)
{
if (v___x_720_ == 0)
{
lean_dec(v_a_717_);
lean_dec_ref(v_args_713_);
return v___x_716_;
}
else
{
size_t v___x_722_; size_t v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v___x_716_);
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_719_);
v___x_724_ = lean_unbox(v_a_717_);
lean_dec(v_a_717_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_713_, v___x_722_, v___x_723_, v___x_724_, v_a_649_);
lean_dec_ref(v_args_713_);
return v___x_725_;
}
}
else
{
size_t v___x_726_; size_t v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v___x_716_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = lean_usize_of_nat(v___x_719_);
v___x_728_ = lean_unbox(v_a_717_);
lean_dec(v_a_717_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_713_, v___x_726_, v___x_727_, v___x_728_, v_a_649_);
lean_dec_ref(v_args_713_);
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(lean_object* v_value_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object* v_env_738_, lean_object* v_value_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object* v_env_747_, lean_object* v_value_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_747_, v_value_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_env_747_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object* v_as_756_, size_t v_i_757_, size_t v_stop_758_, uint8_t v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_756_, v_i_757_, v_stop_758_, v_b_759_, v___y_760_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object* v_as_767_, lean_object* v_i_768_, lean_object* v_stop_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
size_t v_i_boxed_777_; size_t v_stop_boxed_778_; uint8_t v_b_boxed_779_; lean_object* v_res_780_; 
v_i_boxed_777_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_stop_boxed_778_ = lean_unbox_usize(v_stop_769_);
lean_dec(v_stop_769_);
v_b_boxed_779_ = lean_unbox(v_b_770_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_767_, v_i_boxed_777_, v_stop_boxed_778_, v_b_boxed_779_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v_as_767_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object* v_upperBound_781_, lean_object* v_args_782_, lean_object* v_val_783_, lean_object* v_inst_784_, lean_object* v_R_785_, lean_object* v_a_786_, uint8_t v_b_787_, lean_object* v_c_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_781_, v_args_782_, v_val_783_, v_a_786_, v_b_787_, v___y_789_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object* v_upperBound_796_, lean_object* v_args_797_, lean_object* v_val_798_, lean_object* v_inst_799_, lean_object* v_R_800_, lean_object* v_a_801_, lean_object* v_b_802_, lean_object* v_c_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_b_boxed_810_; lean_object* v_res_811_; 
v_b_boxed_810_ = lean_unbox(v_b_802_);
v_res_811_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_796_, v_args_797_, v_val_798_, v_inst_799_, v_R_800_, v_a_801_, v_b_boxed_810_, v_c_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v_val_798_);
lean_dec_ref(v_args_797_);
lean_dec(v_upperBound_796_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object* v_as_812_, size_t v_i_813_, size_t v_stop_814_, uint8_t v_b_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_812_, v_i_813_, v_stop_814_, v_b_815_, v___y_816_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object* v_as_823_, lean_object* v_i_824_, lean_object* v_stop_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
size_t v_i_boxed_833_; size_t v_stop_boxed_834_; uint8_t v_b_boxed_835_; lean_object* v_res_836_; 
v_i_boxed_833_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_stop_boxed_834_ = lean_unbox_usize(v_stop_825_);
lean_dec(v_stop_825_);
v_b_boxed_835_ = lean_unbox(v_b_826_);
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_823_, v_i_boxed_833_, v_stop_boxed_834_, v_b_boxed_835_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v_as_823_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object* v_value_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
if (lean_obj_tag(v_value_837_) == 0)
{
lean_object* v_decl_844_; lean_object* v_value_845_; lean_object* v___x_846_; 
v_decl_844_ = lean_ctor_get(v_value_837_, 0);
lean_inc_ref(v_decl_844_);
lean_dec_ref(v_value_837_);
v_value_845_ = lean_ctor_get(v_decl_844_, 3);
lean_inc(v_value_845_);
lean_dec_ref(v_decl_844_);
v___x_846_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_845_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v___x_846_;
}
else
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_value_837_);
v___x_847_ = 0;
v___x_848_ = lean_box(v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object* v_value_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object* v_env_858_, lean_object* v_value_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object* v_env_867_, lean_object* v_value_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_867_, v_value_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_env_867_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(lean_object* v_a_876_, lean_object* v_b_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_dec(v_b_877_);
lean_dec(v_a_876_);
return v_x_878_;
}
else
{
lean_object* v_key_879_; lean_object* v_value_880_; lean_object* v_tail_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
v_key_879_ = lean_ctor_get(v_x_878_, 0);
v_value_880_ = lean_ctor_get(v_x_878_, 1);
v_tail_881_ = lean_ctor_get(v_x_878_, 2);
v_isSharedCheck_893_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_893_ == 0)
{
v___x_883_ = v_x_878_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_tail_881_);
lean_inc(v_value_880_);
lean_inc(v_key_879_);
lean_dec(v_x_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_instBEqFVarId_beq(v_key_879_, v_a_876_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_876_, v_b_877_, v_tail_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 2, v___x_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_key_879_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_value_880_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec(v_value_880_);
lean_dec(v_key_879_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_b_877_);
lean_ctor_set(v___x_883_, 0, v_a_876_);
v___x_891_ = v___x_883_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_876_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_b_877_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_tail_881_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(lean_object* v_m_894_, lean_object* v_a_895_, lean_object* v_b_896_){
_start:
{
lean_object* v_size_897_; lean_object* v_buckets_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_941_; 
v_size_897_ = lean_ctor_get(v_m_894_, 0);
v_buckets_898_ = lean_ctor_get(v_m_894_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_m_894_);
if (v_isSharedCheck_941_ == 0)
{
v___x_900_ = v_m_894_;
v_isShared_901_ = v_isSharedCheck_941_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_buckets_898_);
lean_inc(v_size_897_);
lean_dec(v_m_894_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_941_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; uint64_t v_fold_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v_bkt_915_; uint8_t v___x_916_; 
v___x_902_ = lean_array_get_size(v_buckets_898_);
v___x_903_ = l_Lean_instHashableFVarId_hash(v_a_895_);
v___x_904_ = 32ULL;
v___x_905_ = lean_uint64_shift_right(v___x_903_, v___x_904_);
v_fold_906_ = lean_uint64_xor(v___x_903_, v___x_905_);
v___x_907_ = 16ULL;
v___x_908_ = lean_uint64_shift_right(v_fold_906_, v___x_907_);
v___x_909_ = lean_uint64_xor(v_fold_906_, v___x_908_);
v___x_910_ = lean_uint64_to_usize(v___x_909_);
v___x_911_ = lean_usize_of_nat(v___x_902_);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_sub(v___x_911_, v___x_912_);
v___x_914_ = lean_usize_land(v___x_910_, v___x_913_);
v_bkt_915_ = lean_array_uget_borrowed(v_buckets_898_, v___x_914_);
v___x_916_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_895_, v_bkt_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v_size_x27_918_; lean_object* v___x_919_; lean_object* v_buckets_x27_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_917_ = lean_unsigned_to_nat(1u);
v_size_x27_918_ = lean_nat_add(v_size_897_, v___x_917_);
lean_dec(v_size_897_);
lean_inc(v_bkt_915_);
v___x_919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_919_, 0, v_a_895_);
lean_ctor_set(v___x_919_, 1, v_b_896_);
lean_ctor_set(v___x_919_, 2, v_bkt_915_);
v_buckets_x27_920_ = lean_array_uset(v_buckets_898_, v___x_914_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(4u);
v___x_922_ = lean_nat_mul(v_size_x27_918_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(3u);
v___x_924_ = lean_nat_div(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_array_get_size(v_buckets_x27_920_);
v___x_926_ = lean_nat_dec_le(v___x_924_, v___x_925_);
lean_dec(v___x_924_);
if (v___x_926_ == 0)
{
lean_object* v_val_927_; lean_object* v___x_929_; 
v_val_927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_920_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_val_927_);
lean_ctor_set(v___x_900_, 0, v_size_x27_918_);
v___x_929_ = v___x_900_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_size_x27_918_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_val_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v___x_932_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_buckets_x27_920_);
lean_ctor_set(v___x_900_, 0, v_size_x27_918_);
v___x_932_ = v___x_900_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_size_x27_918_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_buckets_x27_920_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
else
{
lean_object* v___x_934_; lean_object* v_buckets_x27_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
lean_inc(v_bkt_915_);
v___x_934_ = lean_box(0);
v_buckets_x27_935_ = lean_array_uset(v_buckets_898_, v___x_914_, v___x_934_);
v___x_936_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_895_, v_b_896_, v_bkt_915_);
v___x_937_ = lean_array_uset(v_buckets_x27_935_, v___x_914_, v___x_936_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_937_);
v___x_939_ = v___x_900_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_size_897_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_box(0);
return v___x_944_;
}
else
{
lean_object* v_key_945_; lean_object* v_value_946_; lean_object* v_tail_947_; uint8_t v___x_948_; 
v_key_945_ = lean_ctor_get(v_x_943_, 0);
v_value_946_ = lean_ctor_get(v_x_943_, 1);
v_tail_947_ = lean_ctor_get(v_x_943_, 2);
v___x_948_ = l_Lean_instBEqFVarId_beq(v_key_945_, v_a_942_);
if (v___x_948_ == 0)
{
v_x_943_ = v_tail_947_;
goto _start;
}
else
{
lean_object* v___x_950_; 
lean_inc(v_value_946_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_value_946_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_951_, v_x_952_);
lean_dec(v_x_952_);
lean_dec(v_a_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object* v_m_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_buckets_956_; lean_object* v___x_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v_fold_961_; uint64_t v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; size_t v___x_965_; size_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_buckets_956_ = lean_ctor_get(v_m_954_, 1);
v___x_957_ = lean_array_get_size(v_buckets_956_);
v___x_958_ = l_Lean_instHashableFVarId_hash(v_a_955_);
v___x_959_ = 32ULL;
v___x_960_ = lean_uint64_shift_right(v___x_958_, v___x_959_);
v_fold_961_ = lean_uint64_xor(v___x_958_, v___x_960_);
v___x_962_ = 16ULL;
v___x_963_ = lean_uint64_shift_right(v_fold_961_, v___x_962_);
v___x_964_ = lean_uint64_xor(v_fold_961_, v___x_963_);
v___x_965_ = lean_uint64_to_usize(v___x_964_);
v___x_966_ = lean_usize_of_nat(v___x_957_);
v___x_967_ = ((size_t)1ULL);
v___x_968_ = lean_usize_sub(v___x_966_, v___x_967_);
v___x_969_ = lean_usize_land(v___x_965_, v___x_968_);
v___x_970_ = lean_array_uget_borrowed(v_buckets_956_, v___x_969_);
v___x_971_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_955_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object* v_m_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_m_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* v_plannedDecision_975_, lean_object* v_var_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_st_ref_get(v_a_977_);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_979_, v_var_976_);
lean_dec(v___x_979_);
if (lean_obj_tag(v___x_980_) == 1)
{
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1005_; 
v_val_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1005_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1005_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
if (lean_obj_tag(v_val_981_) == 3)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_985_ = lean_st_ref_take(v_a_977_);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_985_, v_var_976_, v_plannedDecision_975_);
v___x_987_ = lean_st_ref_set(v_a_977_, v___x_986_);
v___x_988_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 0, v___x_988_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
uint8_t v___x_992_; 
v___x_992_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_981_, v_plannedDecision_975_);
lean_dec(v_plannedDecision_975_);
lean_dec(v_val_981_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_993_ = lean_st_ref_take(v_a_977_);
v___x_994_ = lean_box(2);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_993_, v_var_976_, v___x_994_);
v___x_996_ = lean_st_ref_set(v_a_977_, v___x_995_);
v___x_997_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 0, v___x_997_);
v___x_999_ = v___x_983_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_dec(v_var_976_);
v___x_1001_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 0, v___x_1001_);
v___x_1003_ = v___x_983_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v___x_980_);
lean_dec(v_var_976_);
lean_dec(v_plannedDecision_975_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_1008_, lean_object* v_var_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1008_, v_var_1009_, v_a_1010_);
lean_dec(v_a_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_1013_, lean_object* v_var_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1013_, v_var_1014_, v_a_1015_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_1023_, lean_object* v_var_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1023_, v_var_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_1033_, lean_object* v_m_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1034_, v_a_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1037_, v_m_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_m_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object* v_00_u03b2_1041_, lean_object* v_m_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_1042_, v_a_1043_, v_b_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object* v_00_u03b2_1046_, lean_object* v_a_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1050_, lean_object* v_a_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_1050_, v_a_1051_, v_x_1052_);
lean_dec(v_x_1052_);
lean_dec(v_a_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object* v_00_u03b2_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_1055_, v_b_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1059_, lean_object* v_f_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
switch(lean_obj_tag(v_alt_1059_))
{
case 0:
{
lean_object* v_code_1068_; lean_object* v___x_1069_; 
v_code_1068_ = lean_ctor_get(v_alt_1059_, 2);
lean_inc_ref(v_code_1068_);
lean_dec_ref(v_alt_1059_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc(v___y_1061_);
v___x_1069_ = lean_apply_8(v_f_1060_, v_code_1068_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, lean_box(0));
return v___x_1069_;
}
case 1:
{
lean_object* v_code_1070_; lean_object* v___x_1071_; 
v_code_1070_ = lean_ctor_get(v_alt_1059_, 1);
lean_inc_ref(v_code_1070_);
lean_dec_ref(v_alt_1059_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc(v___y_1061_);
v___x_1071_ = lean_apply_8(v_f_1060_, v_code_1070_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, lean_box(0));
return v___x_1071_;
}
default: 
{
lean_object* v_code_1072_; lean_object* v___x_1073_; 
v_code_1072_ = lean_ctor_get(v_alt_1059_, 0);
lean_inc_ref(v_code_1072_);
lean_dec_ref(v_alt_1059_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc(v___y_1061_);
v___x_1073_ = lean_apply_8(v_f_1060_, v_code_1072_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, lean_box(0));
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1074_, lean_object* v_f_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1074_, v_f_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
return v_res_1083_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_instMonadEIO(lean_box(0));
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_toApplicative_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1162_; 
v___x_1097_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1098_ = l_StateRefT_x27_instMonad___redArg(v___x_1097_);
v_toApplicative_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v___x_1098_, 1);
lean_dec(v_unused_1163_);
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1162_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_toApplicative_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1162_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_toFunctor_1103_; lean_object* v_toSeq_1104_; lean_object* v_toSeqLeft_1105_; lean_object* v_toSeqRight_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1160_; 
v_toFunctor_1103_ = lean_ctor_get(v_toApplicative_1099_, 0);
v_toSeq_1104_ = lean_ctor_get(v_toApplicative_1099_, 2);
v_toSeqLeft_1105_ = lean_ctor_get(v_toApplicative_1099_, 3);
v_toSeqRight_1106_ = lean_ctor_get(v_toApplicative_1099_, 4);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_toApplicative_1099_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_toApplicative_1099_, 1);
lean_dec(v_unused_1161_);
v___x_1108_ = v_toApplicative_1099_;
v_isShared_1109_ = v_isSharedCheck_1160_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_toSeqRight_1106_);
lean_inc(v_toSeqLeft_1105_);
lean_inc(v_toSeq_1104_);
lean_inc(v_toFunctor_1103_);
lean_dec(v_toApplicative_1099_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1160_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___x_1119_; 
v___f_1110_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1111_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1103_);
v___f_1112_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1112_, 0, v_toFunctor_1103_);
v___f_1113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1113_, 0, v_toFunctor_1103_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___f_1112_);
lean_ctor_set(v___x_1114_, 1, v___f_1113_);
v___f_1115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1115_, 0, v_toSeqRight_1106_);
v___f_1116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1116_, 0, v_toSeqLeft_1105_);
v___f_1117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1117_, 0, v_toSeq_1104_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___f_1115_);
lean_ctor_set(v___x_1108_, 3, v___f_1116_);
lean_ctor_set(v___x_1108_, 2, v___f_1117_);
lean_ctor_set(v___x_1108_, 1, v___f_1110_);
lean_ctor_set(v___x_1108_, 0, v___x_1114_);
v___x_1119_ = v___x_1108_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___f_1110_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v___f_1117_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v___f_1116_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v___f_1115_);
v___x_1119_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___f_1111_);
lean_ctor_set(v___x_1101_, 0, v___x_1119_);
v___x_1121_ = v___x_1101_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___f_1111_);
v___x_1121_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v_toApplicative_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1156_; 
v___x_1122_ = l_StateRefT_x27_instMonad___redArg(v___x_1121_);
v_toApplicative_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v___x_1122_, 1);
lean_dec(v_unused_1157_);
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1156_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_toApplicative_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1156_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_toFunctor_1127_; lean_object* v_toSeq_1128_; lean_object* v_toSeqLeft_1129_; lean_object* v_toSeqRight_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1154_; 
v_toFunctor_1127_ = lean_ctor_get(v_toApplicative_1123_, 0);
v_toSeq_1128_ = lean_ctor_get(v_toApplicative_1123_, 2);
v_toSeqLeft_1129_ = lean_ctor_get(v_toApplicative_1123_, 3);
v_toSeqRight_1130_ = lean_ctor_get(v_toApplicative_1123_, 4);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_toApplicative_1123_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_toApplicative_1123_, 1);
lean_dec(v_unused_1155_);
v___x_1132_ = v_toApplicative_1123_;
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_toSeqRight_1130_);
lean_inc(v_toSeqLeft_1129_);
lean_inc(v_toSeq_1128_);
lean_inc(v_toFunctor_1127_);
lean_dec(v_toApplicative_1123_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___f_1141_; lean_object* v___x_1143_; 
v___f_1134_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1135_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1127_);
v___f_1136_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1136_, 0, v_toFunctor_1127_);
v___f_1137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1137_, 0, v_toFunctor_1127_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___f_1136_);
lean_ctor_set(v___x_1138_, 1, v___f_1137_);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1139_, 0, v_toSeqRight_1130_);
v___f_1140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1140_, 0, v_toSeqLeft_1129_);
v___f_1141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1141_, 0, v_toSeq_1128_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v___f_1139_);
lean_ctor_set(v___x_1132_, 3, v___f_1140_);
lean_ctor_set(v___x_1132_, 2, v___f_1141_);
lean_ctor_set(v___x_1132_, 1, v___f_1134_);
lean_ctor_set(v___x_1132_, 0, v___x_1138_);
v___x_1143_ = v___x_1132_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___f_1134_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v___f_1141_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v___f_1140_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___f_1139_);
v___x_1143_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___f_1135_);
lean_ctor_set(v___x_1125_, 0, v___x_1143_);
v___x_1145_ = v___x_1125_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___f_1135_);
v___x_1145_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_9300__overap_1150_; lean_object* v___x_1151_; 
v___x_1146_ = l_ReaderT_instMonad___redArg(v___x_1145_);
v___x_1147_ = l_StateRefT_x27_instMonad___redArg(v___x_1146_);
v___x_1148_ = lean_box(0);
v___x_1149_ = l_instInhabitedOfMonad___redArg(v___x_1147_, v___x_1148_);
v___x_9300__overap_1150_ = lean_panic_fn_borrowed(v___x_1149_, v_msg_1089_);
lean_dec(v___x_1149_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc(v___y_1090_);
v___x_1151_ = lean_apply_7(v___x_9300__overap_1150_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, lean_box(0));
return v___x_1151_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
return v_res_1172_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1177_ = lean_unsigned_to_nat(40u);
v___x_1178_ = lean_unsigned_to_nat(49u);
v___x_1179_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1180_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1181_ = l_mkPanicMessageWithDecl(v___x_1180_, v___x_1179_, v___x_1178_, v___x_1177_, v___x_1176_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1182_, lean_object* v_e_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_ty_1192_; lean_object* v_body_1193_; uint8_t v___x_1196_; 
v___x_1196_ = l_Lean_Expr_hasFVar(v_e_1183_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_f_1182_);
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
else
{
switch(lean_obj_tag(v_e_1183_))
{
case 1:
{
lean_object* v_fvarId_1199_; lean_object* v___x_1200_; 
v_fvarId_1199_ = lean_ctor_get(v_e_1183_, 0);
lean_inc(v_fvarId_1199_);
lean_dec_ref(v_e_1183_);
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
lean_inc(v___y_1187_);
lean_inc_ref(v___y_1186_);
lean_inc(v___y_1185_);
lean_inc(v___y_1184_);
v___x_1200_ = lean_apply_8(v_f_1182_, v_fvarId_1199_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, lean_box(0));
return v___x_1200_;
}
case 2:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_f_1182_);
v___x_1201_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1202_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1201_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1202_;
}
case 5:
{
lean_object* v_fn_1203_; lean_object* v_arg_1204_; lean_object* v___x_1205_; 
v_fn_1203_ = lean_ctor_get(v_e_1183_, 0);
lean_inc_ref(v_fn_1203_);
v_arg_1204_ = lean_ctor_get(v_e_1183_, 1);
lean_inc_ref(v_arg_1204_);
lean_dec_ref(v_e_1183_);
lean_inc_ref(v_f_1182_);
v___x_1205_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1182_, v_fn_1203_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_dec_ref(v___x_1205_);
v_e_1183_ = v_arg_1204_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1204_);
lean_dec_ref(v_f_1182_);
return v___x_1205_;
}
}
case 6:
{
lean_object* v_binderType_1207_; lean_object* v_body_1208_; 
v_binderType_1207_ = lean_ctor_get(v_e_1183_, 1);
lean_inc_ref(v_binderType_1207_);
v_body_1208_ = lean_ctor_get(v_e_1183_, 2);
lean_inc_ref(v_body_1208_);
lean_dec_ref(v_e_1183_);
v_ty_1192_ = v_binderType_1207_;
v_body_1193_ = v_body_1208_;
goto v___jp_1191_;
}
case 7:
{
lean_object* v_binderType_1209_; lean_object* v_body_1210_; 
v_binderType_1209_ = lean_ctor_get(v_e_1183_, 1);
lean_inc_ref(v_binderType_1209_);
v_body_1210_ = lean_ctor_get(v_e_1183_, 2);
lean_inc_ref(v_body_1210_);
lean_dec_ref(v_e_1183_);
v_ty_1192_ = v_binderType_1209_;
v_body_1193_ = v_body_1210_;
goto v___jp_1191_;
}
case 8:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_f_1182_);
v___x_1211_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1212_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1211_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1212_;
}
case 11:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_f_1182_);
v___x_1213_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1214_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1213_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1214_;
}
default: 
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v_e_1183_);
lean_dec_ref(v_f_1182_);
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
}
v___jp_1191_:
{
lean_object* v___x_1194_; 
lean_inc_ref(v_f_1182_);
v___x_1194_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1182_, v_ty_1192_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_dec_ref(v___x_1194_);
v_e_1183_ = v_body_1193_;
goto _start;
}
else
{
lean_dec_ref(v_body_1193_);
lean_dec_ref(v_f_1182_);
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1217_, lean_object* v_e_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1217_, v_e_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1227_, lean_object* v_param_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_type_1236_; lean_object* v___x_1237_; 
v_type_1236_ = lean_ctor_get(v_param_1228_, 2);
lean_inc_ref(v_type_1236_);
lean_dec_ref(v_param_1228_);
v___x_1237_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1227_, v_type_1236_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1238_, lean_object* v_param_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1238_, v_param_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1248_, lean_object* v_f_1249_, lean_object* v_as_1250_, size_t v_i_1251_, size_t v_stop_1252_, lean_object* v_b_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_usize_dec_eq(v_i_1251_, v_stop_1252_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_array_uget_borrowed(v_as_1250_, v_i_1251_);
lean_inc(v___x_1262_);
lean_inc_ref(v_f_1249_);
v___x_1263_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1249_, v___x_1262_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; size_t v___x_1265_; size_t v___x_1266_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_add(v_i_1251_, v___x_1265_);
v_i_1251_ = v___x_1266_;
v_b_1253_ = v_a_1264_;
goto _start;
}
else
{
lean_dec_ref(v_f_1249_);
return v___x_1263_;
}
}
else
{
lean_object* v___x_1268_; 
lean_dec_ref(v_f_1249_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_b_1253_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1269_, lean_object* v_f_1270_, lean_object* v_as_1271_, lean_object* v_i_1272_, lean_object* v_stop_1273_, lean_object* v_b_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v_pu_boxed_1282_; size_t v_i_boxed_1283_; size_t v_stop_boxed_1284_; lean_object* v_res_1285_; 
v_pu_boxed_1282_ = lean_unbox(v_pu_1269_);
v_i_boxed_1283_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_stop_boxed_1284_ = lean_unbox_usize(v_stop_1273_);
lean_dec(v_stop_1273_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1282_, v_f_1270_, v_as_1271_, v_i_boxed_1283_, v_stop_boxed_1284_, v_b_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v_as_1271_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1286_, lean_object* v_arg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
switch(lean_obj_tag(v_arg_1287_))
{
case 0:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v_f_1286_);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
case 1:
{
lean_object* v_fvarId_1297_; lean_object* v___x_1298_; 
v_fvarId_1297_ = lean_ctor_get(v_arg_1287_, 0);
lean_inc(v_fvarId_1297_);
lean_dec_ref(v_arg_1287_);
lean_inc(v___y_1293_);
lean_inc_ref(v___y_1292_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc(v___y_1288_);
v___x_1298_ = lean_apply_8(v_f_1286_, v_fvarId_1297_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, lean_box(0));
return v___x_1298_;
}
default: 
{
lean_object* v_expr_1299_; lean_object* v___x_1300_; 
v_expr_1299_ = lean_ctor_get(v_arg_1287_, 0);
lean_inc_ref(v_expr_1299_);
lean_dec_ref(v_arg_1287_);
v___x_1300_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1286_, v_expr_1299_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1301_, lean_object* v_arg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1301_, v_arg_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1311_, lean_object* v_f_1312_, lean_object* v_as_1313_, size_t v_i_1314_, size_t v_stop_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_eq(v_i_1314_, v_stop_1315_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_array_uget_borrowed(v_as_1313_, v_i_1314_);
lean_inc(v___x_1325_);
lean_inc_ref(v_f_1312_);
v___x_1326_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1312_, v___x_1325_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; size_t v___x_1328_; size_t v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_i_1314_, v___x_1328_);
v_i_1314_ = v___x_1329_;
v_b_1316_ = v_a_1327_;
goto _start;
}
else
{
lean_dec_ref(v_f_1312_);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v_f_1312_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_b_1316_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1332_, lean_object* v_f_1333_, lean_object* v_as_1334_, lean_object* v_i_1335_, lean_object* v_stop_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v_pu_boxed_1345_; size_t v_i_boxed_1346_; size_t v_stop_boxed_1347_; lean_object* v_res_1348_; 
v_pu_boxed_1345_ = lean_unbox(v_pu_1332_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_stop_boxed_1347_ = lean_unbox_usize(v_stop_1336_);
lean_dec(v_stop_1336_);
v_res_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1345_, v_f_1333_, v_as_1334_, v_i_boxed_1346_, v_stop_boxed_1347_, v_b_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v_as_1334_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1349_, lean_object* v_f_1350_, lean_object* v_e_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_args_1360_; 
switch(lean_obj_tag(v_e_1351_))
{
case 2:
{
lean_object* v_struct_1374_; lean_object* v___x_1375_; 
v_struct_1374_ = lean_ctor_get(v_e_1351_, 2);
lean_inc(v_struct_1374_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1375_ = lean_apply_8(v_f_1350_, v_struct_1374_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1375_;
}
case 3:
{
lean_object* v_args_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_args_1376_ = lean_ctor_get(v_e_1351_, 2);
lean_inc_ref(v_args_1376_);
lean_dec_ref(v_e_1351_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_array_get_size(v_args_1376_);
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_nat_dec_lt(v___x_1377_, v___x_1378_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref(v_args_1376_);
lean_dec_ref(v_f_1350_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
return v___x_1381_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_nat_dec_le(v___x_1378_, v___x_1378_);
if (v___x_1382_ == 0)
{
if (v___x_1380_ == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref(v_args_1376_);
lean_dec_ref(v_f_1350_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1379_);
return v___x_1383_;
}
else
{
size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = lean_usize_of_nat(v___x_1378_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1376_, v___x_1384_, v___x_1385_, v___x_1379_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1376_);
return v___x_1386_;
}
}
else
{
size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = lean_usize_of_nat(v___x_1378_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1376_, v___x_1387_, v___x_1388_, v___x_1379_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1376_);
return v___x_1389_;
}
}
}
case 4:
{
lean_object* v_fvarId_1390_; lean_object* v_args_1391_; lean_object* v___x_1392_; 
v_fvarId_1390_ = lean_ctor_get(v_e_1351_, 0);
lean_inc(v_fvarId_1390_);
v_args_1391_ = lean_ctor_get(v_e_1351_, 1);
lean_inc_ref(v_args_1391_);
lean_dec_ref(v_e_1351_);
lean_inc_ref(v_f_1350_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1392_ = lean_apply_8(v_f_1350_, v_fvarId_1390_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1413_; 
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1392_, 0);
lean_dec(v_unused_1414_);
v___x_1394_ = v___x_1392_;
v_isShared_1395_ = v_isSharedCheck_1413_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v___x_1392_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1413_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_array_get_size(v_args_1391_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_nat_dec_lt(v___x_1396_, v___x_1397_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1401_; 
lean_dec_ref(v_args_1391_);
lean_dec_ref(v_f_1350_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1398_);
v___x_1401_ = v___x_1394_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1398_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_nat_dec_le(v___x_1397_, v___x_1397_);
if (v___x_1403_ == 0)
{
if (v___x_1399_ == 0)
{
lean_object* v___x_1405_; 
lean_dec_ref(v_args_1391_);
lean_dec_ref(v_f_1350_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1398_);
v___x_1405_ = v___x_1394_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1398_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
else
{
size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
lean_del_object(v___x_1394_);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = lean_usize_of_nat(v___x_1397_);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1391_, v___x_1407_, v___x_1408_, v___x_1398_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1391_);
return v___x_1409_;
}
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
lean_del_object(v___x_1394_);
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1397_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1391_, v___x_1410_, v___x_1411_, v___x_1398_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1391_);
return v___x_1412_;
}
}
}
}
else
{
lean_dec_ref(v_args_1391_);
lean_dec_ref(v_f_1350_);
return v___x_1392_;
}
}
case 5:
{
lean_object* v_args_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_args_1415_ = lean_ctor_get(v_e_1351_, 1);
lean_inc_ref(v_args_1415_);
lean_dec_ref(v_e_1351_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v_args_1415_);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec_ref(v_args_1415_);
lean_dec_ref(v_f_1350_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_le(v___x_1417_, v___x_1417_);
if (v___x_1421_ == 0)
{
if (v___x_1419_ == 0)
{
lean_object* v___x_1422_; 
lean_dec_ref(v_args_1415_);
lean_dec_ref(v_f_1350_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1418_);
return v___x_1422_;
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1417_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1415_, v___x_1423_, v___x_1424_, v___x_1418_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1415_);
return v___x_1425_;
}
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1417_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1415_, v___x_1426_, v___x_1427_, v___x_1418_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1415_);
return v___x_1428_;
}
}
}
case 6:
{
lean_object* v_var_1429_; lean_object* v___x_1430_; 
v_var_1429_ = lean_ctor_get(v_e_1351_, 1);
lean_inc(v_var_1429_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1430_ = lean_apply_8(v_f_1350_, v_var_1429_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1430_;
}
case 7:
{
lean_object* v_var_1431_; lean_object* v___x_1432_; 
v_var_1431_ = lean_ctor_get(v_e_1351_, 1);
lean_inc(v_var_1431_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1432_ = lean_apply_8(v_f_1350_, v_var_1431_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1432_;
}
case 8:
{
lean_object* v_var_1433_; lean_object* v___x_1434_; 
v_var_1433_ = lean_ctor_get(v_e_1351_, 2);
lean_inc(v_var_1433_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1434_ = lean_apply_8(v_f_1350_, v_var_1433_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1434_;
}
case 9:
{
lean_object* v_args_1435_; 
v_args_1435_ = lean_ctor_get(v_e_1351_, 1);
lean_inc_ref(v_args_1435_);
lean_dec_ref(v_e_1351_);
v_args_1360_ = v_args_1435_;
goto v___jp_1359_;
}
case 10:
{
lean_object* v_args_1436_; 
v_args_1436_ = lean_ctor_get(v_e_1351_, 1);
lean_inc_ref(v_args_1436_);
lean_dec_ref(v_e_1351_);
v_args_1360_ = v_args_1436_;
goto v___jp_1359_;
}
case 11:
{
lean_object* v_var_1437_; lean_object* v___x_1438_; 
v_var_1437_ = lean_ctor_get(v_e_1351_, 1);
lean_inc(v_var_1437_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1438_ = lean_apply_8(v_f_1350_, v_var_1437_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1438_;
}
case 12:
{
lean_object* v_var_1439_; lean_object* v_args_1440_; lean_object* v___x_1441_; 
v_var_1439_ = lean_ctor_get(v_e_1351_, 0);
lean_inc(v_var_1439_);
v_args_1440_ = lean_ctor_get(v_e_1351_, 2);
lean_inc_ref(v_args_1440_);
lean_dec_ref(v_e_1351_);
lean_inc_ref(v_f_1350_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1441_ = lean_apply_8(v_f_1350_, v_var_1439_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1463_);
v___x_1443_ = v___x_1441_;
v_isShared_1444_ = v_isSharedCheck_1462_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v___x_1441_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1462_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_array_get_size(v_args_1440_);
v___x_1447_ = lean_box(0);
v___x_1448_ = lean_nat_dec_lt(v___x_1445_, v___x_1446_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref(v_args_1440_);
lean_dec_ref(v_f_1350_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1447_);
v___x_1450_ = v___x_1443_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1447_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_nat_dec_le(v___x_1446_, v___x_1446_);
if (v___x_1452_ == 0)
{
if (v___x_1448_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref(v_args_1440_);
lean_dec_ref(v_f_1350_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1447_);
v___x_1454_ = v___x_1443_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1447_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
else
{
size_t v___x_1456_; size_t v___x_1457_; lean_object* v___x_1458_; 
lean_del_object(v___x_1443_);
v___x_1456_ = ((size_t)0ULL);
v___x_1457_ = lean_usize_of_nat(v___x_1446_);
v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1440_, v___x_1456_, v___x_1457_, v___x_1447_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1440_);
return v___x_1458_;
}
}
else
{
size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
lean_del_object(v___x_1443_);
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = lean_usize_of_nat(v___x_1446_);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1440_, v___x_1459_, v___x_1460_, v___x_1447_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1440_);
return v___x_1461_;
}
}
}
}
else
{
lean_dec_ref(v_args_1440_);
lean_dec_ref(v_f_1350_);
return v___x_1441_;
}
}
case 13:
{
lean_object* v_fvarId_1464_; lean_object* v___x_1465_; 
v_fvarId_1464_ = lean_ctor_get(v_e_1351_, 1);
lean_inc(v_fvarId_1464_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1465_ = lean_apply_8(v_f_1350_, v_fvarId_1464_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1465_;
}
case 14:
{
lean_object* v_fvarId_1466_; lean_object* v___x_1467_; 
v_fvarId_1466_ = lean_ctor_get(v_e_1351_, 0);
lean_inc(v_fvarId_1466_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1467_ = lean_apply_8(v_f_1350_, v_fvarId_1466_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1467_;
}
case 15:
{
lean_object* v_fvarId_1468_; lean_object* v___x_1469_; 
v_fvarId_1468_ = lean_ctor_get(v_e_1351_, 0);
lean_inc(v_fvarId_1468_);
lean_dec_ref(v_e_1351_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc(v___y_1352_);
v___x_1469_ = lean_apply_8(v_f_1350_, v_fvarId_1468_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, lean_box(0));
return v___x_1469_;
}
default: 
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v_e_1351_);
lean_dec_ref(v_f_1350_);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_array_get_size(v_args_1360_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_nat_dec_lt(v___x_1361_, v___x_1362_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref(v_args_1360_);
lean_dec_ref(v_f_1350_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
return v___x_1365_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_nat_dec_le(v___x_1362_, v___x_1362_);
if (v___x_1366_ == 0)
{
if (v___x_1364_ == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref(v_args_1360_);
lean_dec_ref(v_f_1350_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1363_);
return v___x_1367_;
}
else
{
size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = lean_usize_of_nat(v___x_1362_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1360_, v___x_1368_, v___x_1369_, v___x_1363_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1360_);
return v___x_1370_;
}
}
else
{
size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = lean_usize_of_nat(v___x_1362_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1349_, v_f_1350_, v_args_1360_, v___x_1371_, v___x_1372_, v___x_1363_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec_ref(v_args_1360_);
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1472_, lean_object* v_f_1473_, lean_object* v_e_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_pu_boxed_1482_; lean_object* v_res_1483_; 
v_pu_boxed_1482_ = lean_unbox(v_pu_1472_);
v_res_1483_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1482_, v_f_1473_, v_e_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec(v___y_1475_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1484_, lean_object* v_f_1485_, lean_object* v_decl_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_type_1494_; lean_object* v_value_1495_; lean_object* v___x_1496_; 
v_type_1494_ = lean_ctor_get(v_decl_1486_, 2);
lean_inc_ref(v_type_1494_);
v_value_1495_ = lean_ctor_get(v_decl_1486_, 3);
lean_inc(v_value_1495_);
lean_dec_ref(v_decl_1486_);
lean_inc_ref(v_f_1485_);
v___x_1496_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1485_, v_type_1494_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; 
lean_dec_ref(v___x_1496_);
v___x_1497_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1484_, v_f_1485_, v_value_1495_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1497_;
}
else
{
lean_dec(v_value_1495_);
lean_dec_ref(v_f_1485_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1498_, lean_object* v_f_1499_, lean_object* v_decl_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v_pu_boxed_1508_; lean_object* v_res_1509_; 
v_pu_boxed_1508_ = lean_unbox(v_pu_1498_);
v_res_1509_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1508_, v_f_1499_, v_decl_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v___y_1501_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1510_, lean_object* v_f_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_pu_boxed_1520_; lean_object* v_res_1521_; 
v_pu_boxed_1520_ = lean_unbox(v_pu_1510_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1520_, v_f_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1522_, lean_object* v_f_1523_, lean_object* v_as_1524_, size_t v_i_1525_, size_t v_stop_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_usize_dec_eq(v_i_1525_, v_stop_1526_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1536_ = lean_box(v_pu_1522_);
lean_inc_ref(v_f_1523_);
v___f_1537_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1537_, 0, v___x_1536_);
lean_closure_set(v___f_1537_, 1, v_f_1523_);
v___x_1538_ = lean_array_uget_borrowed(v_as_1524_, v_i_1525_);
lean_inc(v___x_1538_);
v___x_1539_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1538_, v___f_1537_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; size_t v___x_1541_; size_t v___x_1542_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_add(v_i_1525_, v___x_1541_);
v_i_1525_ = v___x_1542_;
v_b_1527_ = v_a_1540_;
goto _start;
}
else
{
lean_dec_ref(v_f_1523_);
return v___x_1539_;
}
}
else
{
lean_object* v___x_1544_; 
lean_dec_ref(v_f_1523_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_b_1527_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1545_, lean_object* v_f_1546_, lean_object* v_c_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
switch(lean_obj_tag(v_c_1547_))
{
case 0:
{
lean_object* v_decl_1555_; lean_object* v_k_1556_; lean_object* v___x_1557_; 
v_decl_1555_ = lean_ctor_get(v_c_1547_, 0);
lean_inc_ref(v_decl_1555_);
v_k_1556_ = lean_ctor_get(v_c_1547_, 1);
lean_inc_ref(v_k_1556_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
v___x_1557_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1545_, v_f_1546_, v_decl_1555_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref(v___x_1557_);
v_c_1547_ = v_k_1556_;
goto _start;
}
else
{
lean_dec_ref(v_k_1556_);
lean_dec_ref(v_f_1546_);
return v___x_1557_;
}
}
case 1:
{
lean_object* v_decl_1559_; lean_object* v_k_1560_; lean_object* v_params_1561_; lean_object* v_type_1562_; lean_object* v_value_1563_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_decl_1559_ = lean_ctor_get(v_c_1547_, 0);
lean_inc_ref(v_decl_1559_);
v_k_1560_ = lean_ctor_get(v_c_1547_, 1);
lean_inc_ref(v_k_1560_);
lean_dec_ref(v_c_1547_);
v_params_1561_ = lean_ctor_get(v_decl_1559_, 2);
lean_inc_ref(v_params_1561_);
v_type_1562_ = lean_ctor_get(v_decl_1559_, 3);
lean_inc_ref(v_type_1562_);
v_value_1563_ = lean_ctor_get(v_decl_1559_, 4);
lean_inc_ref(v_value_1563_);
lean_dec_ref(v_decl_1559_);
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = lean_array_get_size(v_params_1561_);
v___x_1576_ = lean_nat_dec_lt(v___x_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v_params_1561_);
lean_inc_ref(v_f_1546_);
v___x_1577_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_type_1562_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___x_1577_);
lean_inc_ref(v_f_1546_);
v___x_1578_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1545_, v_f_1546_, v_value_1563_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_dec_ref(v___x_1578_);
v_c_1547_ = v_k_1560_;
goto _start;
}
else
{
lean_dec_ref(v_k_1560_);
lean_dec_ref(v_f_1546_);
return v___x_1578_;
}
}
else
{
lean_dec_ref(v_value_1563_);
lean_dec_ref(v_k_1560_);
lean_dec_ref(v_f_1546_);
return v___x_1577_;
}
}
else
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_nat_dec_le(v___x_1575_, v___x_1575_);
if (v___x_1581_ == 0)
{
if (v___x_1576_ == 0)
{
lean_dec_ref(v_params_1561_);
v___y_1565_ = v___y_1548_;
v___y_1566_ = v___y_1549_;
v___y_1567_ = v___y_1550_;
v___y_1568_ = v___y_1551_;
v___y_1569_ = v___y_1552_;
v___y_1570_ = v___y_1553_;
goto v___jp_1564_;
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1575_);
lean_inc_ref(v_f_1546_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1545_, v_f_1546_, v_params_1561_, v___x_1582_, v___x_1583_, v___x_1580_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_params_1561_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_dec_ref(v___x_1584_);
v___y_1565_ = v___y_1548_;
v___y_1566_ = v___y_1549_;
v___y_1567_ = v___y_1550_;
v___y_1568_ = v___y_1551_;
v___y_1569_ = v___y_1552_;
v___y_1570_ = v___y_1553_;
goto v___jp_1564_;
}
else
{
lean_dec_ref(v_value_1563_);
lean_dec_ref(v_type_1562_);
lean_dec_ref(v_k_1560_);
lean_dec_ref(v_f_1546_);
return v___x_1584_;
}
}
}
else
{
size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = lean_usize_of_nat(v___x_1575_);
lean_inc_ref(v_f_1546_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1545_, v_f_1546_, v_params_1561_, v___x_1585_, v___x_1586_, v___x_1580_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_params_1561_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_dec_ref(v___x_1587_);
v___y_1565_ = v___y_1548_;
v___y_1566_ = v___y_1549_;
v___y_1567_ = v___y_1550_;
v___y_1568_ = v___y_1551_;
v___y_1569_ = v___y_1552_;
v___y_1570_ = v___y_1553_;
goto v___jp_1564_;
}
else
{
lean_dec_ref(v_value_1563_);
lean_dec_ref(v_type_1562_);
lean_dec_ref(v_k_1560_);
lean_dec_ref(v_f_1546_);
return v___x_1587_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1571_; 
lean_inc_ref(v_f_1546_);
v___x_1571_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_type_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref(v___x_1571_);
lean_inc_ref(v_f_1546_);
v___x_1572_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1545_, v_f_1546_, v_value_1563_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec_ref(v___x_1572_);
v_c_1547_ = v_k_1560_;
v___y_1548_ = v___y_1565_;
v___y_1549_ = v___y_1566_;
v___y_1550_ = v___y_1567_;
v___y_1551_ = v___y_1568_;
v___y_1552_ = v___y_1569_;
v___y_1553_ = v___y_1570_;
goto _start;
}
else
{
lean_dec_ref(v_k_1560_);
lean_dec_ref(v_f_1546_);
return v___x_1572_;
}
}
else
{
lean_dec_ref(v_value_1563_);
lean_dec_ref(v_k_1560_);
lean_dec_ref(v_f_1546_);
return v___x_1571_;
}
}
}
case 2:
{
lean_object* v_decl_1588_; lean_object* v_k_1589_; lean_object* v_params_1590_; lean_object* v_type_1591_; lean_object* v_value_1592_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_decl_1588_ = lean_ctor_get(v_c_1547_, 0);
lean_inc_ref(v_decl_1588_);
v_k_1589_ = lean_ctor_get(v_c_1547_, 1);
lean_inc_ref(v_k_1589_);
lean_dec_ref(v_c_1547_);
v_params_1590_ = lean_ctor_get(v_decl_1588_, 2);
lean_inc_ref(v_params_1590_);
v_type_1591_ = lean_ctor_get(v_decl_1588_, 3);
lean_inc_ref(v_type_1591_);
v_value_1592_ = lean_ctor_get(v_decl_1588_, 4);
lean_inc_ref(v_value_1592_);
lean_dec_ref(v_decl_1588_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_array_get_size(v_params_1590_);
v___x_1605_ = lean_nat_dec_lt(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v_params_1590_);
lean_inc_ref(v_f_1546_);
v___x_1606_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_type_1591_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
lean_dec_ref(v___x_1606_);
lean_inc_ref(v_f_1546_);
v___x_1607_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1545_, v_f_1546_, v_value_1592_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref(v___x_1607_);
v_c_1547_ = v_k_1589_;
goto _start;
}
else
{
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_f_1546_);
return v___x_1607_;
}
}
else
{
lean_dec_ref(v_value_1592_);
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_f_1546_);
return v___x_1606_;
}
}
else
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_nat_dec_le(v___x_1604_, v___x_1604_);
if (v___x_1610_ == 0)
{
if (v___x_1605_ == 0)
{
lean_dec_ref(v_params_1590_);
v___y_1594_ = v___y_1548_;
v___y_1595_ = v___y_1549_;
v___y_1596_ = v___y_1550_;
v___y_1597_ = v___y_1551_;
v___y_1598_ = v___y_1552_;
v___y_1599_ = v___y_1553_;
goto v___jp_1593_;
}
else
{
size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = ((size_t)0ULL);
v___x_1612_ = lean_usize_of_nat(v___x_1604_);
lean_inc_ref(v_f_1546_);
v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1545_, v_f_1546_, v_params_1590_, v___x_1611_, v___x_1612_, v___x_1609_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_params_1590_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec_ref(v___x_1613_);
v___y_1594_ = v___y_1548_;
v___y_1595_ = v___y_1549_;
v___y_1596_ = v___y_1550_;
v___y_1597_ = v___y_1551_;
v___y_1598_ = v___y_1552_;
v___y_1599_ = v___y_1553_;
goto v___jp_1593_;
}
else
{
lean_dec_ref(v_value_1592_);
lean_dec_ref(v_type_1591_);
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_f_1546_);
return v___x_1613_;
}
}
}
else
{
size_t v___x_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = ((size_t)0ULL);
v___x_1615_ = lean_usize_of_nat(v___x_1604_);
lean_inc_ref(v_f_1546_);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1545_, v_f_1546_, v_params_1590_, v___x_1614_, v___x_1615_, v___x_1609_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_params_1590_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_dec_ref(v___x_1616_);
v___y_1594_ = v___y_1548_;
v___y_1595_ = v___y_1549_;
v___y_1596_ = v___y_1550_;
v___y_1597_ = v___y_1551_;
v___y_1598_ = v___y_1552_;
v___y_1599_ = v___y_1553_;
goto v___jp_1593_;
}
else
{
lean_dec_ref(v_value_1592_);
lean_dec_ref(v_type_1591_);
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_f_1546_);
return v___x_1616_;
}
}
}
v___jp_1593_:
{
lean_object* v___x_1600_; 
lean_inc_ref(v_f_1546_);
v___x_1600_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_type_1591_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v___x_1600_);
lean_inc_ref(v_f_1546_);
v___x_1601_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1545_, v_f_1546_, v_value_1592_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref(v___x_1601_);
v_c_1547_ = v_k_1589_;
v___y_1548_ = v___y_1594_;
v___y_1549_ = v___y_1595_;
v___y_1550_ = v___y_1596_;
v___y_1551_ = v___y_1597_;
v___y_1552_ = v___y_1598_;
v___y_1553_ = v___y_1599_;
goto _start;
}
else
{
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_f_1546_);
return v___x_1601_;
}
}
else
{
lean_dec_ref(v_value_1592_);
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_f_1546_);
return v___x_1600_;
}
}
}
case 3:
{
lean_object* v_fvarId_1617_; lean_object* v_args_1618_; lean_object* v___x_1619_; 
v_fvarId_1617_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1617_);
v_args_1618_ = lean_ctor_get(v_c_1547_, 1);
lean_inc_ref(v_args_1618_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1619_ = lean_apply_8(v_f_1546_, v_fvarId_1617_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1640_; 
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v___x_1619_, 0);
lean_dec(v_unused_1641_);
v___x_1621_ = v___x_1619_;
v_isShared_1622_ = v_isSharedCheck_1640_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v___x_1619_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1640_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_array_get_size(v_args_1618_);
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_nat_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1628_; 
lean_dec_ref(v_args_1618_);
lean_dec_ref(v_f_1546_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1625_);
v___x_1628_ = v___x_1621_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1625_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_nat_dec_le(v___x_1624_, v___x_1624_);
if (v___x_1630_ == 0)
{
if (v___x_1626_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v_args_1618_);
lean_dec_ref(v_f_1546_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1625_);
v___x_1632_ = v___x_1621_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1625_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
else
{
size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
lean_del_object(v___x_1621_);
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = lean_usize_of_nat(v___x_1624_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1545_, v_f_1546_, v_args_1618_, v___x_1634_, v___x_1635_, v___x_1625_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_args_1618_);
return v___x_1636_;
}
}
else
{
size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
lean_del_object(v___x_1621_);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = lean_usize_of_nat(v___x_1624_);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1545_, v_f_1546_, v_args_1618_, v___x_1637_, v___x_1638_, v___x_1625_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_args_1618_);
return v___x_1639_;
}
}
}
}
else
{
lean_dec_ref(v_args_1618_);
lean_dec_ref(v_f_1546_);
return v___x_1619_;
}
}
case 4:
{
lean_object* v_cases_1642_; lean_object* v_resultType_1643_; lean_object* v_discr_1644_; lean_object* v_alts_1645_; lean_object* v___x_1646_; 
v_cases_1642_ = lean_ctor_get(v_c_1547_, 0);
lean_inc_ref(v_cases_1642_);
lean_dec_ref(v_c_1547_);
v_resultType_1643_ = lean_ctor_get(v_cases_1642_, 1);
lean_inc_ref(v_resultType_1643_);
v_discr_1644_ = lean_ctor_get(v_cases_1642_, 2);
lean_inc(v_discr_1644_);
v_alts_1645_ = lean_ctor_get(v_cases_1642_, 3);
lean_inc_ref(v_alts_1645_);
lean_dec_ref(v_cases_1642_);
lean_inc_ref(v_f_1546_);
v___x_1646_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_resultType_1643_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v___x_1646_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1647_ = lean_apply_8(v_f_1546_, v_discr_1644_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1668_; 
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1647_, 0);
lean_dec(v_unused_1669_);
v___x_1649_ = v___x_1647_;
v_isShared_1650_ = v_isSharedCheck_1668_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v___x_1647_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1668_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_array_get_size(v_alts_1645_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_nat_dec_lt(v___x_1651_, v___x_1652_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1656_; 
lean_dec_ref(v_alts_1645_);
lean_dec_ref(v_f_1546_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1653_);
v___x_1656_ = v___x_1649_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
else
{
uint8_t v___x_1658_; 
v___x_1658_ = lean_nat_dec_le(v___x_1652_, v___x_1652_);
if (v___x_1658_ == 0)
{
if (v___x_1654_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v_alts_1645_);
lean_dec_ref(v_f_1546_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1653_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1653_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
else
{
size_t v___x_1662_; size_t v___x_1663_; lean_object* v___x_1664_; 
lean_del_object(v___x_1649_);
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = lean_usize_of_nat(v___x_1652_);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1545_, v_f_1546_, v_alts_1645_, v___x_1662_, v___x_1663_, v___x_1653_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_alts_1645_);
return v___x_1664_;
}
}
else
{
size_t v___x_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
lean_del_object(v___x_1649_);
v___x_1665_ = ((size_t)0ULL);
v___x_1666_ = lean_usize_of_nat(v___x_1652_);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1545_, v_f_1546_, v_alts_1645_, v___x_1665_, v___x_1666_, v___x_1653_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v_alts_1645_);
return v___x_1667_;
}
}
}
}
else
{
lean_dec_ref(v_alts_1645_);
lean_dec_ref(v_f_1546_);
return v___x_1647_;
}
}
else
{
lean_dec_ref(v_alts_1645_);
lean_dec(v_discr_1644_);
lean_dec_ref(v_f_1546_);
return v___x_1646_;
}
}
case 5:
{
lean_object* v_fvarId_1670_; lean_object* v___x_1671_; 
v_fvarId_1670_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1670_);
lean_dec_ref(v_c_1547_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1671_ = lean_apply_8(v_f_1546_, v_fvarId_1670_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
return v___x_1671_;
}
case 6:
{
lean_object* v_type_1672_; lean_object* v___x_1673_; 
v_type_1672_ = lean_ctor_get(v_c_1547_, 0);
lean_inc_ref(v_type_1672_);
lean_dec_ref(v_c_1547_);
v___x_1673_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_type_1672_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1673_;
}
case 7:
{
lean_object* v_fvarId_1674_; lean_object* v_y_1675_; lean_object* v_k_1676_; lean_object* v___x_1677_; 
v_fvarId_1674_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1674_);
v_y_1675_ = lean_ctor_get(v_c_1547_, 2);
lean_inc(v_y_1675_);
v_k_1676_ = lean_ctor_get(v_c_1547_, 3);
lean_inc_ref(v_k_1676_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1677_ = lean_apply_8(v_f_1546_, v_fvarId_1674_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; 
lean_dec_ref(v___x_1677_);
lean_inc_ref(v_f_1546_);
v___x_1678_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1546_, v_y_1675_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref(v___x_1678_);
v_c_1547_ = v_k_1676_;
goto _start;
}
else
{
lean_dec_ref(v_k_1676_);
lean_dec_ref(v_f_1546_);
return v___x_1678_;
}
}
else
{
lean_dec_ref(v_k_1676_);
lean_dec(v_y_1675_);
lean_dec_ref(v_f_1546_);
return v___x_1677_;
}
}
case 8:
{
lean_object* v_fvarId_1680_; lean_object* v_y_1681_; lean_object* v_k_1682_; lean_object* v___x_1683_; 
v_fvarId_1680_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1680_);
v_y_1681_ = lean_ctor_get(v_c_1547_, 2);
lean_inc(v_y_1681_);
v_k_1682_ = lean_ctor_get(v_c_1547_, 3);
lean_inc_ref(v_k_1682_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1683_ = lean_apply_8(v_f_1546_, v_fvarId_1680_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v___x_1683_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1684_ = lean_apply_8(v_f_1546_, v_y_1681_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_dec_ref(v___x_1684_);
v_c_1547_ = v_k_1682_;
goto _start;
}
else
{
lean_dec_ref(v_k_1682_);
lean_dec_ref(v_f_1546_);
return v___x_1684_;
}
}
else
{
lean_dec_ref(v_k_1682_);
lean_dec(v_y_1681_);
lean_dec_ref(v_f_1546_);
return v___x_1683_;
}
}
case 9:
{
lean_object* v_fvarId_1686_; lean_object* v_y_1687_; lean_object* v_ty_1688_; lean_object* v_k_1689_; lean_object* v___x_1690_; 
v_fvarId_1686_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1686_);
v_y_1687_ = lean_ctor_get(v_c_1547_, 3);
lean_inc(v_y_1687_);
v_ty_1688_ = lean_ctor_get(v_c_1547_, 4);
lean_inc_ref(v_ty_1688_);
v_k_1689_ = lean_ctor_get(v_c_1547_, 5);
lean_inc_ref(v_k_1689_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1690_ = lean_apply_8(v_f_1546_, v_fvarId_1686_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref(v___x_1690_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1691_ = lean_apply_8(v_f_1546_, v_y_1687_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref(v___x_1691_);
lean_inc_ref(v_f_1546_);
v___x_1692_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1546_, v_ty_1688_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_dec_ref(v___x_1692_);
v_c_1547_ = v_k_1689_;
goto _start;
}
else
{
lean_dec_ref(v_k_1689_);
lean_dec_ref(v_f_1546_);
return v___x_1692_;
}
}
else
{
lean_dec_ref(v_k_1689_);
lean_dec_ref(v_ty_1688_);
lean_dec_ref(v_f_1546_);
return v___x_1691_;
}
}
else
{
lean_dec_ref(v_k_1689_);
lean_dec_ref(v_ty_1688_);
lean_dec(v_y_1687_);
lean_dec_ref(v_f_1546_);
return v___x_1690_;
}
}
case 13:
{
lean_object* v_fvarId_1694_; lean_object* v_k_1695_; lean_object* v___x_1696_; 
v_fvarId_1694_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1694_);
v_k_1695_ = lean_ctor_get(v_c_1547_, 1);
lean_inc_ref(v_k_1695_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1696_ = lean_apply_8(v_f_1546_, v_fvarId_1694_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_dec_ref(v___x_1696_);
v_c_1547_ = v_k_1695_;
goto _start;
}
else
{
lean_dec_ref(v_k_1695_);
lean_dec_ref(v_f_1546_);
return v___x_1696_;
}
}
default: 
{
lean_object* v_fvarId_1698_; lean_object* v_k_1699_; lean_object* v___x_1700_; 
v_fvarId_1698_ = lean_ctor_get(v_c_1547_, 0);
lean_inc(v_fvarId_1698_);
v_k_1699_ = lean_ctor_get(v_c_1547_, 2);
lean_inc_ref(v_k_1699_);
lean_dec_ref(v_c_1547_);
lean_inc_ref(v_f_1546_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc(v___y_1548_);
v___x_1700_ = lean_apply_8(v_f_1546_, v_fvarId_1698_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, lean_box(0));
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_dec_ref(v___x_1700_);
v_c_1547_ = v_k_1699_;
goto _start;
}
else
{
lean_dec_ref(v_k_1699_);
lean_dec_ref(v_f_1546_);
return v___x_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1702_, lean_object* v_f_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1702_, v_f_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1713_, lean_object* v_f_1714_, lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_stop_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v_pu_boxed_1726_; size_t v_i_boxed_1727_; size_t v_stop_boxed_1728_; lean_object* v_res_1729_; 
v_pu_boxed_1726_ = lean_unbox(v_pu_1713_);
v_i_boxed_1727_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_stop_boxed_1728_ = lean_unbox_usize(v_stop_1717_);
lean_dec(v_stop_1717_);
v_res_1729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1726_, v_f_1714_, v_as_1715_, v_i_boxed_1727_, v_stop_boxed_1728_, v_b_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v_as_1715_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1730_, lean_object* v_f_1731_, lean_object* v_c_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v_pu_boxed_1740_; lean_object* v_res_1741_; 
v_pu_boxed_1740_ = lean_unbox(v_pu_1730_);
v_res_1741_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1740_, v_f_1731_, v_c_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec(v___y_1733_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1742_, lean_object* v_as_1743_, size_t v_i_1744_, size_t v_stop_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_eq(v_i_1744_, v_stop_1745_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc(v___x_1742_);
v___x_1755_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1755_, 0, v___x_1742_);
v___x_1756_ = lean_array_uget_borrowed(v_as_1743_, v_i_1744_);
lean_inc(v___x_1756_);
v___x_1757_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1755_, v___x_1756_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; size_t v___x_1759_; size_t v___x_1760_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1744_, v___x_1759_);
v_i_1744_ = v___x_1760_;
v_b_1746_ = v_a_1758_;
goto _start;
}
else
{
lean_dec(v___x_1742_);
return v___x_1757_;
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v___x_1742_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_b_1746_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1763_, lean_object* v_as_1764_, lean_object* v_i_1765_, lean_object* v_stop_1766_, lean_object* v_b_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
size_t v_i_boxed_1775_; size_t v_stop_boxed_1776_; lean_object* v_res_1777_; 
v_i_boxed_1775_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_stop_boxed_1776_ = lean_unbox_usize(v_stop_1766_);
lean_dec(v_stop_1766_);
v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1763_, v_as_1764_, v_i_boxed_1775_, v_stop_boxed_1776_, v_b_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v_as_1764_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = 0;
v___x_1787_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1778_);
lean_inc(v___x_1787_);
v___x_1788_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1788_, 0, v___x_1787_);
switch(lean_obj_tag(v_alt_1778_))
{
case 0:
{
lean_object* v_params_1789_; lean_object* v_code_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_params_1789_ = lean_ctor_get(v_alt_1778_, 1);
lean_inc_ref(v_params_1789_);
v_code_1790_ = lean_ctor_get(v_alt_1778_, 2);
lean_inc_ref(v_code_1790_);
lean_dec_ref(v_alt_1778_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_array_get_size(v_params_1789_);
v___x_1793_ = lean_nat_dec_lt(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
lean_dec_ref(v_params_1789_);
lean_dec(v___x_1787_);
v___x_1794_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1786_, v___x_1788_, v_code_1790_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_nat_dec_le(v___x_1792_, v___x_1792_);
if (v___x_1796_ == 0)
{
if (v___x_1793_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v_params_1789_);
lean_dec(v___x_1787_);
v___x_1797_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1786_, v___x_1788_, v_code_1790_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1797_;
}
else
{
size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = lean_usize_of_nat(v___x_1792_);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1787_, v_params_1789_, v___x_1798_, v___x_1799_, v___x_1795_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec_ref(v_params_1789_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v___x_1800_);
v___x_1801_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1786_, v___x_1788_, v_code_1790_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1801_;
}
else
{
lean_dec_ref(v_code_1790_);
lean_dec_ref(v___x_1788_);
return v___x_1800_;
}
}
}
else
{
size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = lean_usize_of_nat(v___x_1792_);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1787_, v_params_1789_, v___x_1802_, v___x_1803_, v___x_1795_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec_ref(v_params_1789_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref(v___x_1804_);
v___x_1805_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1786_, v___x_1788_, v_code_1790_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1805_;
}
else
{
lean_dec_ref(v_code_1790_);
lean_dec_ref(v___x_1788_);
return v___x_1804_;
}
}
}
}
case 1:
{
lean_object* v_code_1806_; lean_object* v___x_1807_; 
lean_dec(v___x_1787_);
v_code_1806_ = lean_ctor_get(v_alt_1778_, 1);
lean_inc_ref(v_code_1806_);
lean_dec_ref(v_alt_1778_);
v___x_1807_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1786_, v___x_1788_, v_code_1806_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1807_;
}
default: 
{
lean_object* v_code_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1787_);
v_code_1808_ = lean_ctor_get(v_alt_1778_, 0);
lean_inc_ref(v_code_1808_);
lean_dec_ref(v_alt_1778_);
v___x_1809_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1786_, v___x_1788_, v_code_1808_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec(v_a_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1819_, lean_object* v_f_1820_, lean_object* v_param_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1820_, v_param_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1830_, lean_object* v_f_1831_, lean_object* v_param_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_pu_boxed_1840_; lean_object* v_res_1841_; 
v_pu_boxed_1840_ = lean_unbox(v_pu_1830_);
v_res_1841_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1840_, v_f_1831_, v_param_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec(v___y_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1842_, lean_object* v_alt_1843_, lean_object* v_f_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1843_, v_f_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1853_, lean_object* v_alt_1854_, lean_object* v_f_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_pu_boxed_1863_; lean_object* v_res_1864_; 
v_pu_boxed_1863_ = lean_unbox(v_pu_1853_);
v_res_1864_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1863_, v_alt_1854_, v_f_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1865_, lean_object* v_f_1866_, lean_object* v_arg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1866_, v_arg_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1876_, lean_object* v_f_1877_, lean_object* v_arg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
uint8_t v_pu_boxed_1886_; lean_object* v_res_1887_; 
v_pu_boxed_1886_ = lean_unbox(v_pu_1876_);
v_res_1887_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1886_, v_f_1877_, v_arg_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1888_, size_t v_i_1889_, size_t v_stop_1890_, lean_object* v_b_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_usize_dec_eq(v_i_1889_, v_stop_1890_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_array_uget_borrowed(v_as_1888_, v_i_1889_);
lean_inc(v___x_1900_);
v___x_1901_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1900_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; size_t v___x_1903_; size_t v___x_1904_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1901_);
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1889_, v___x_1903_);
v_i_1889_ = v___x_1904_;
v_b_1891_ = v_a_1902_;
goto _start;
}
else
{
return v___x_1901_;
}
}
else
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_b_1891_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1907_, lean_object* v_i_1908_, lean_object* v_stop_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
size_t v_i_boxed_1918_; size_t v_stop_boxed_1919_; lean_object* v_res_1920_; 
v_i_boxed_1918_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_stop_boxed_1919_ = lean_unbox_usize(v_stop_1909_);
lean_dec(v_stop_1909_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1907_, v_i_boxed_1918_, v_stop_boxed_1919_, v_b_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v_as_1907_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_alts_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_alts_1929_ = lean_ctor_get(v_cs_1921_, 3);
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = lean_array_get_size(v_alts_1929_);
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
return v___x_1934_;
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_nat_dec_le(v___x_1931_, v___x_1931_);
if (v___x_1935_ == 0)
{
if (v___x_1933_ == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1932_);
return v___x_1936_;
}
else
{
size_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = lean_usize_of_nat(v___x_1931_);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1929_, v___x_1937_, v___x_1938_, v___x_1932_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
return v___x_1939_;
}
}
else
{
size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = lean_usize_of_nat(v___x_1931_);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1929_, v___x_1940_, v___x_1941_, v___x_1932_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_cs_1943_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
if (lean_obj_tag(v_x_1953_) == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_x_1952_);
return v___x_1959_;
}
else
{
lean_object* v_head_1960_; lean_object* v_tail_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2023_; 
v_head_1960_ = lean_ctor_get(v_x_1953_, 0);
v_tail_1961_ = lean_ctor_get(v_x_1953_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_x_1953_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1963_ = v_x_1953_;
v_isShared_1964_ = v_isSharedCheck_2023_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_tail_1961_);
lean_inc(v_head_1960_);
lean_dec(v_x_1953_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2023_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_fst_1965_; lean_object* v_snd_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2022_; 
v_fst_1965_ = lean_ctor_get(v_x_1952_, 0);
v_snd_1966_ = lean_ctor_get(v_x_1952_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1952_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1968_ = v_x_1952_;
v_isShared_1969_ = v_isSharedCheck_2022_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1966_);
lean_inc(v_fst_1965_);
lean_dec(v_x_1952_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2022_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; 
if (lean_obj_tag(v_head_1960_) == 0)
{
lean_object* v_decl_2003_; lean_object* v___x_2004_; 
v_decl_2003_ = lean_ctor_get(v_head_1960_, 0);
lean_inc_ref(v_decl_2003_);
v___x_2004_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_2003_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; uint8_t v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2006_ == 0)
{
lean_del_object(v___x_1963_);
v___y_1971_ = v___y_1954_;
v___y_1972_ = v___y_1955_;
v___y_1973_ = v___y_1956_;
v___y_1974_ = v___y_1957_;
goto v___jp_1970_;
}
else
{
lean_object* v_fvarId_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_inc_ref(v_decl_2003_);
lean_dec_ref(v_head_1960_);
lean_del_object(v___x_1968_);
v_fvarId_2007_ = lean_ctor_get(v_decl_2003_, 0);
lean_inc(v_fvarId_2007_);
lean_dec_ref(v_decl_2003_);
v___x_2008_ = lean_box(2);
v___x_2009_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1965_, v_fvarId_2007_, v___x_2008_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 0);
lean_ctor_set(v___x_1963_, 1, v_snd_1966_);
lean_ctor_set(v___x_1963_, 0, v___x_2009_);
v___x_2011_ = v___x_1963_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_snd_1966_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v_x_1952_ = v___x_2011_;
v_x_1953_ = v_tail_1961_;
goto _start;
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v_head_1960_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_dec(v_tail_1961_);
v_a_2014_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2004_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2004_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_del_object(v___x_1963_);
v___y_1971_ = v___y_1954_;
v___y_1972_ = v___y_1955_;
v___y_1973_ = v___y_1956_;
v___y_1974_ = v___y_1957_;
goto v___jp_1970_;
}
v___jp_1970_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = lean_st_ref_get(v___y_1974_);
lean_dec(v___x_1975_);
v___x_1976_ = lean_st_mk_ref(v_snd_1966_);
lean_inc(v_head_1960_);
v___x_1977_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1960_, v___x_1976_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
v___x_1979_ = lean_st_ref_get(v___x_1976_);
lean_dec(v___x_1976_);
v___x_1980_ = lean_unbox(v_a_1978_);
lean_dec(v_a_1978_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1981_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1960_);
lean_dec(v_head_1960_);
v___x_1982_ = lean_box(3);
v___x_1983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1965_, v___x_1981_, v___x_1982_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___x_1979_);
lean_ctor_set(v___x_1968_, 0, v___x_1983_);
v___x_1985_ = v___x_1968_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1979_);
v___x_1985_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
v_x_1952_ = v___x_1985_;
v_x_1953_ = v_tail_1961_;
goto _start;
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1988_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1960_);
lean_dec(v_head_1960_);
v___x_1989_ = lean_box(2);
v___x_1990_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1965_, v___x_1988_, v___x_1989_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___x_1979_);
lean_ctor_set(v___x_1968_, 0, v___x_1990_);
v___x_1992_ = v___x_1968_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1979_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_x_1952_ = v___x_1992_;
v_x_1953_ = v_tail_1961_;
goto _start;
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v___x_1976_);
lean_del_object(v___x_1968_);
lean_dec(v_fst_1965_);
lean_dec(v_tail_1961_);
lean_dec(v_head_1960_);
v_a_1995_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1977_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1977_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2024_, v_x_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_unsigned_to_nat(16u);
v___x_2034_ = lean_mk_array(v___x_2033_, v___x_2032_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v___x_2035_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_map_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2071_ = l_List_lengthTR___redArg(v_a_2039_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_unsigned_to_nat(4u);
v___x_2074_ = lean_nat_mul(v___x_2071_, v___x_2073_);
lean_dec(v___x_2071_);
v___x_2075_ = lean_unsigned_to_nat(3u);
v___x_2076_ = lean_nat_div(v___x_2074_, v___x_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = l_Nat_nextPowerOfTwo(v___x_2076_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_mk_array(v___x_2077_, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2072_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
lean_inc(v_a_2039_);
v___x_2083_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2082_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v_fst_2085_; lean_object* v_discr_2086_; uint8_t v___x_2087_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
v_fst_2085_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_fst_2085_);
lean_dec(v_a_2084_);
v_discr_2086_ = lean_ctor_get(v_cs_2038_, 2);
v___x_2087_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2085_, v_discr_2086_);
if (v___x_2087_ == 0)
{
v_map_2046_ = v_fst_2085_;
v___y_2047_ = v_a_2039_;
v___y_2048_ = v_a_2040_;
v___y_2049_ = v_a_2041_;
v___y_2050_ = v_a_2042_;
v___y_2051_ = v_a_2043_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_box(2);
lean_inc(v_discr_2086_);
v___x_2089_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2085_, v_discr_2086_, v___x_2088_);
v_map_2046_ = v___x_2089_;
v___y_2047_ = v_a_2039_;
v___y_2048_ = v_a_2040_;
v___y_2049_ = v_a_2041_;
v___y_2050_ = v_a_2042_;
v___y_2051_ = v_a_2043_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_cs_2038_);
v_a_2090_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2083_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2083_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
v___jp_2045_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_st_mk_ref(v_map_2046_);
v___x_2053_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_2038_, v___x_2052_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec_ref(v_cs_2038_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2061_; 
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2053_, 0);
lean_dec(v_unused_2062_);
v___x_2055_ = v___x_2053_;
v_isShared_2056_ = v_isSharedCheck_2061_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v___x_2053_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2061_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = lean_st_ref_get(v___x_2052_);
lean_dec(v___x_2052_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2057_);
v___x_2059_ = v___x_2055_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v___x_2052_);
v_a_2063_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2053_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2053_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2106_, v_x_2107_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2115_, v_x_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_a_2124_, lean_object* v_x_2125_){
_start:
{
if (lean_obj_tag(v_x_2125_) == 0)
{
uint8_t v___x_2126_; 
v___x_2126_ = 0;
return v___x_2126_;
}
else
{
lean_object* v_key_2127_; lean_object* v_tail_2128_; uint8_t v___x_2129_; 
v_key_2127_ = lean_ctor_get(v_x_2125_, 0);
v_tail_2128_ = lean_ctor_get(v_x_2125_, 2);
v___x_2129_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2127_, v_a_2124_);
if (v___x_2129_ == 0)
{
v_x_2125_ = v_tail_2128_;
goto _start;
}
else
{
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_a_2131_, lean_object* v_x_2132_){
_start:
{
uint8_t v_res_2133_; lean_object* v_r_2134_; 
v_res_2133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2131_, v_x_2132_);
lean_dec(v_x_2132_);
lean_dec(v_a_2131_);
v_r_2134_ = lean_box(v_res_2133_);
return v_r_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object* v_a_2135_, lean_object* v_b_2136_, lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 0)
{
lean_dec(v_b_2136_);
lean_dec(v_a_2135_);
return v_x_2137_;
}
else
{
lean_object* v_key_2138_; lean_object* v_value_2139_; lean_object* v_tail_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2152_; 
v_key_2138_ = lean_ctor_get(v_x_2137_, 0);
v_value_2139_ = lean_ctor_get(v_x_2137_, 1);
v_tail_2140_ = lean_ctor_get(v_x_2137_, 2);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_x_2137_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2142_ = v_x_2137_;
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_tail_2140_);
lean_inc(v_value_2139_);
lean_inc(v_key_2138_);
lean_dec(v_x_2137_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2138_, v_a_2135_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2135_, v_b_2136_, v_tail_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 2, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_key_2138_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_value_2139_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
else
{
lean_object* v___x_2150_; 
lean_dec(v_value_2139_);
lean_dec(v_key_2138_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 1, v_b_2136_);
lean_ctor_set(v___x_2142_, 0, v_a_2135_);
v___x_2150_ = v___x_2142_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2135_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_b_2136_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_tail_2140_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
if (lean_obj_tag(v_x_2154_) == 0)
{
return v_x_2153_;
}
else
{
lean_object* v_key_2155_; lean_object* v_value_2156_; lean_object* v_tail_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2180_; 
v_key_2155_ = lean_ctor_get(v_x_2154_, 0);
v_value_2156_ = lean_ctor_get(v_x_2154_, 1);
v_tail_2157_ = lean_ctor_get(v_x_2154_, 2);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_x_2154_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2159_ = v_x_2154_;
v_isShared_2160_ = v_isSharedCheck_2180_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_tail_2157_);
lean_inc(v_value_2156_);
lean_inc(v_key_2155_);
lean_dec(v_x_2154_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2180_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; uint64_t v___x_2162_; uint64_t v___x_2163_; uint64_t v___x_2164_; uint64_t v_fold_2165_; uint64_t v___x_2166_; uint64_t v___x_2167_; uint64_t v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2161_ = lean_array_get_size(v_x_2153_);
v___x_2162_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_2155_);
v___x_2163_ = 32ULL;
v___x_2164_ = lean_uint64_shift_right(v___x_2162_, v___x_2163_);
v_fold_2165_ = lean_uint64_xor(v___x_2162_, v___x_2164_);
v___x_2166_ = 16ULL;
v___x_2167_ = lean_uint64_shift_right(v_fold_2165_, v___x_2166_);
v___x_2168_ = lean_uint64_xor(v_fold_2165_, v___x_2167_);
v___x_2169_ = lean_uint64_to_usize(v___x_2168_);
v___x_2170_ = lean_usize_of_nat(v___x_2161_);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_sub(v___x_2170_, v___x_2171_);
v___x_2173_ = lean_usize_land(v___x_2169_, v___x_2172_);
v___x_2174_ = lean_array_uget_borrowed(v_x_2153_, v___x_2173_);
lean_inc(v___x_2174_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 2, v___x_2174_);
v___x_2176_ = v___x_2159_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_key_2155_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_value_2156_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_array_uset(v_x_2153_, v___x_2173_, v___x_2176_);
v_x_2153_ = v___x_2177_;
v_x_2154_ = v_tail_2157_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2181_, lean_object* v_source_2182_, lean_object* v_target_2183_){
_start:
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = lean_array_get_size(v_source_2182_);
v___x_2185_ = lean_nat_dec_lt(v_i_2181_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v_source_2182_);
lean_dec(v_i_2181_);
return v_target_2183_;
}
else
{
lean_object* v_es_2186_; lean_object* v___x_2187_; lean_object* v_source_2188_; lean_object* v_target_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_es_2186_ = lean_array_fget(v_source_2182_, v_i_2181_);
v___x_2187_ = lean_box(0);
v_source_2188_ = lean_array_fset(v_source_2182_, v_i_2181_, v___x_2187_);
v_target_2189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2183_, v_es_2186_);
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_nat_add(v_i_2181_, v___x_2190_);
lean_dec(v_i_2181_);
v_i_2181_ = v___x_2191_;
v_source_2182_ = v_source_2188_;
v_target_2183_ = v_target_2189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object* v_data_2193_){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_nbuckets_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2194_ = lean_array_get_size(v_data_2193_);
v___x_2195_ = lean_unsigned_to_nat(2u);
v_nbuckets_2196_ = lean_nat_mul(v___x_2194_, v___x_2195_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = lean_box(0);
v___x_2199_ = lean_mk_array(v_nbuckets_2196_, v___x_2198_);
v___x_2200_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2197_, v_data_2193_, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2201_, lean_object* v_a_2202_, lean_object* v_b_2203_){
_start:
{
lean_object* v_size_2204_; lean_object* v_buckets_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2248_; 
v_size_2204_ = lean_ctor_get(v_m_2201_, 0);
v_buckets_2205_ = lean_ctor_get(v_m_2201_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_m_2201_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2207_ = v_m_2201_;
v_isShared_2208_ = v_isSharedCheck_2248_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_buckets_2205_);
lean_inc(v_size_2204_);
lean_dec(v_m_2201_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2248_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v_fold_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; uint64_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; lean_object* v_bkt_2222_; uint8_t v___x_2223_; 
v___x_2209_ = lean_array_get_size(v_buckets_2205_);
v___x_2210_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2202_);
v___x_2211_ = 32ULL;
v___x_2212_ = lean_uint64_shift_right(v___x_2210_, v___x_2211_);
v_fold_2213_ = lean_uint64_xor(v___x_2210_, v___x_2212_);
v___x_2214_ = 16ULL;
v___x_2215_ = lean_uint64_shift_right(v_fold_2213_, v___x_2214_);
v___x_2216_ = lean_uint64_xor(v_fold_2213_, v___x_2215_);
v___x_2217_ = lean_uint64_to_usize(v___x_2216_);
v___x_2218_ = lean_usize_of_nat(v___x_2209_);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_sub(v___x_2218_, v___x_2219_);
v___x_2221_ = lean_usize_land(v___x_2217_, v___x_2220_);
v_bkt_2222_ = lean_array_uget_borrowed(v_buckets_2205_, v___x_2221_);
v___x_2223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2202_, v_bkt_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v_size_x27_2225_; lean_object* v___x_2226_; lean_object* v_buckets_x27_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2224_ = lean_unsigned_to_nat(1u);
v_size_x27_2225_ = lean_nat_add(v_size_2204_, v___x_2224_);
lean_dec(v_size_2204_);
lean_inc(v_bkt_2222_);
v___x_2226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2226_, 0, v_a_2202_);
lean_ctor_set(v___x_2226_, 1, v_b_2203_);
lean_ctor_set(v___x_2226_, 2, v_bkt_2222_);
v_buckets_x27_2227_ = lean_array_uset(v_buckets_2205_, v___x_2221_, v___x_2226_);
v___x_2228_ = lean_unsigned_to_nat(4u);
v___x_2229_ = lean_nat_mul(v_size_x27_2225_, v___x_2228_);
v___x_2230_ = lean_unsigned_to_nat(3u);
v___x_2231_ = lean_nat_div(v___x_2229_, v___x_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_array_get_size(v_buckets_x27_2227_);
v___x_2233_ = lean_nat_dec_le(v___x_2231_, v___x_2232_);
lean_dec(v___x_2231_);
if (v___x_2233_ == 0)
{
lean_object* v_val_2234_; lean_object* v___x_2236_; 
v_val_2234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2227_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v_val_2234_);
lean_ctor_set(v___x_2207_, 0, v_size_x27_2225_);
v___x_2236_ = v___x_2207_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_size_x27_2225_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_val_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v___x_2239_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v_buckets_x27_2227_);
lean_ctor_set(v___x_2207_, 0, v_size_x27_2225_);
v___x_2239_ = v___x_2207_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_size_x27_2225_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_buckets_x27_2227_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v_buckets_x27_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
lean_inc(v_bkt_2222_);
v___x_2241_ = lean_box(0);
v_buckets_x27_2242_ = lean_array_uset(v_buckets_2205_, v___x_2221_, v___x_2241_);
v___x_2243_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2202_, v_b_2203_, v_bkt_2222_);
v___x_2244_ = lean_array_uset(v_buckets_x27_2242_, v___x_2221_, v___x_2243_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2244_);
v___x_2246_ = v___x_2207_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_size_2204_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2249_, size_t v_i_2250_, size_t v_stop_2251_, lean_object* v_b_2252_){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_eq(v_i_2250_, v_stop_2251_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = ((size_t)1ULL);
v___x_2256_ = lean_usize_sub(v_i_2250_, v___x_2255_);
v___x_2257_ = lean_array_uget_borrowed(v_as_2249_, v___x_2256_);
v___x_2258_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2257_);
v___x_2259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2252_, v___x_2258_, v___x_2254_);
v_i_2250_ = v___x_2256_;
v_b_2252_ = v___x_2259_;
goto _start;
}
else
{
return v_b_2252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2261_, lean_object* v_i_2262_, lean_object* v_stop_2263_, lean_object* v_b_2264_){
_start:
{
size_t v_i_boxed_2265_; size_t v_stop_boxed_2266_; lean_object* v_res_2267_; 
v_i_boxed_2265_ = lean_unbox_usize(v_i_2262_);
lean_dec(v_i_2262_);
v_stop_boxed_2266_ = lean_unbox_usize(v_stop_2263_);
lean_dec(v_stop_2263_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2261_, v_i_boxed_2265_, v_stop_boxed_2266_, v_b_2264_);
lean_dec_ref(v_as_2261_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2268_){
_start:
{
lean_object* v_alts_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_map_2284_; uint8_t v___x_2285_; 
v_alts_2269_ = lean_ctor_get(v_cs_2268_, 3);
v___x_2270_ = lean_array_get_size(v_alts_2269_);
v___x_2271_ = lean_unsigned_to_nat(1u);
v___x_2272_ = lean_nat_add(v___x_2270_, v___x_2271_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_unsigned_to_nat(4u);
v___x_2275_ = lean_nat_mul(v___x_2272_, v___x_2274_);
lean_dec(v___x_2272_);
v___x_2276_ = lean_unsigned_to_nat(3u);
v___x_2277_ = lean_nat_div(v___x_2275_, v___x_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = l_Nat_nextPowerOfTwo(v___x_2277_);
lean_dec(v___x_2277_);
v___x_2279_ = lean_box(0);
v___x_2280_ = lean_mk_array(v___x_2278_, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2273_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_box(2);
v___x_2283_ = lean_box(0);
v_map_2284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2281_, v___x_2282_, v___x_2283_);
v___x_2285_ = lean_nat_dec_lt(v___x_2273_, v___x_2270_);
if (v___x_2285_ == 0)
{
return v_map_2284_;
}
else
{
size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_usize_of_nat(v___x_2270_);
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2269_, v___x_2286_, v___x_2287_, v_map_2284_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2289_);
lean_dec_ref(v_cs_2289_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2291_, lean_object* v_m_2292_, lean_object* v_a_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2292_, v_a_2293_, v_b_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2296_, lean_object* v_a_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2297_, v_x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2300_, lean_object* v_a_2301_, lean_object* v_x_2302_){
_start:
{
uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_res_2303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2300_, v_a_2301_, v_x_2302_);
lean_dec(v_x_2302_);
lean_dec(v_a_2301_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2305_, lean_object* v_data_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2308_, lean_object* v_a_2309_, lean_object* v_b_2310_, lean_object* v_x_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2309_, v_b_2310_, v_x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2313_, lean_object* v_i_2314_, lean_object* v_source_2315_, lean_object* v_target_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2314_, v_source_2315_, v_target_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2319_, v_x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v_decision_2326_; uint8_t v___x_2327_; 
v___x_2325_ = lean_st_ref_get(v_a_2323_);
v_decision_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_decision_2326_);
lean_dec(v___x_2325_);
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2326_, v_fvar_2322_);
lean_dec_ref(v_decision_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_fvar_2322_);
v___x_2328_ = lean_box(0);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v_decision_2331_; lean_object* v_newArms_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2344_; 
v___x_2330_ = lean_st_ref_take(v_a_2323_);
v_decision_2331_ = lean_ctor_get(v___x_2330_, 0);
v_newArms_2332_ = lean_ctor_get(v___x_2330_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2334_ = v___x_2330_;
v_isShared_2335_ = v_isSharedCheck_2344_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_newArms_2332_);
lean_inc(v_decision_2331_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2344_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2336_ = lean_box(2);
v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2331_, v_fvar_2322_, v___x_2336_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2337_);
v___x_2339_ = v___x_2334_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_newArms_2332_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_st_ref_set(v_a_2323_, v___x_2339_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2345_, v_a_2346_);
lean_dec(v_a_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2349_, v_a_2350_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec(v_a_2359_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_toApplicative_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2440_; 
v___x_2375_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2376_ = l_StateRefT_x27_instMonad___redArg(v___x_2375_);
v_toApplicative_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v___x_2376_, 1);
lean_dec(v_unused_2441_);
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2440_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_toApplicative_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2440_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_toFunctor_2381_; lean_object* v_toSeq_2382_; lean_object* v_toSeqLeft_2383_; lean_object* v_toSeqRight_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2438_; 
v_toFunctor_2381_ = lean_ctor_get(v_toApplicative_2377_, 0);
v_toSeq_2382_ = lean_ctor_get(v_toApplicative_2377_, 2);
v_toSeqLeft_2383_ = lean_ctor_get(v_toApplicative_2377_, 3);
v_toSeqRight_2384_ = lean_ctor_get(v_toApplicative_2377_, 4);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_toApplicative_2377_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; 
v_unused_2439_ = lean_ctor_get(v_toApplicative_2377_, 1);
lean_dec(v_unused_2439_);
v___x_2386_ = v_toApplicative_2377_;
v_isShared_2387_ = v_isSharedCheck_2438_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_toSeqRight_2384_);
lean_inc(v_toSeqLeft_2383_);
lean_inc(v_toSeq_2382_);
lean_inc(v_toFunctor_2381_);
lean_dec(v_toApplicative_2377_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2438_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___f_2388_; lean_object* v___f_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___f_2393_; lean_object* v___f_2394_; lean_object* v___f_2395_; lean_object* v___x_2397_; 
v___f_2388_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2389_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2381_);
v___f_2390_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2390_, 0, v_toFunctor_2381_);
v___f_2391_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2391_, 0, v_toFunctor_2381_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___f_2390_);
lean_ctor_set(v___x_2392_, 1, v___f_2391_);
v___f_2393_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2393_, 0, v_toSeqRight_2384_);
v___f_2394_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2394_, 0, v_toSeqLeft_2383_);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2395_, 0, v_toSeq_2382_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 4, v___f_2393_);
lean_ctor_set(v___x_2386_, 3, v___f_2394_);
lean_ctor_set(v___x_2386_, 2, v___f_2395_);
lean_ctor_set(v___x_2386_, 1, v___f_2388_);
lean_ctor_set(v___x_2386_, 0, v___x_2392_);
v___x_2397_ = v___x_2386_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___f_2388_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v___f_2395_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v___f_2394_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v___f_2393_);
v___x_2397_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2399_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v___f_2389_);
lean_ctor_set(v___x_2379_, 0, v___x_2397_);
v___x_2399_ = v___x_2379_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v___f_2389_);
v___x_2399_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v_toApplicative_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2434_; 
v___x_2400_ = l_StateRefT_x27_instMonad___redArg(v___x_2399_);
v_toApplicative_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v___x_2400_, 1);
lean_dec(v_unused_2435_);
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2434_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_toApplicative_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2434_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_toFunctor_2405_; lean_object* v_toSeq_2406_; lean_object* v_toSeqLeft_2407_; lean_object* v_toSeqRight_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2432_; 
v_toFunctor_2405_ = lean_ctor_get(v_toApplicative_2401_, 0);
v_toSeq_2406_ = lean_ctor_get(v_toApplicative_2401_, 2);
v_toSeqLeft_2407_ = lean_ctor_get(v_toApplicative_2401_, 3);
v_toSeqRight_2408_ = lean_ctor_get(v_toApplicative_2401_, 4);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_toApplicative_2401_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v_toApplicative_2401_, 1);
lean_dec(v_unused_2433_);
v___x_2410_ = v_toApplicative_2401_;
v_isShared_2411_ = v_isSharedCheck_2432_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_toSeqRight_2408_);
lean_inc(v_toSeqLeft_2407_);
lean_inc(v_toSeq_2406_);
lean_inc(v_toFunctor_2405_);
lean_dec(v_toApplicative_2401_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2432_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___f_2417_; lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___x_2421_; 
v___f_2412_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2413_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2405_);
v___f_2414_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2414_, 0, v_toFunctor_2405_);
v___f_2415_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2415_, 0, v_toFunctor_2405_);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___f_2414_);
lean_ctor_set(v___x_2416_, 1, v___f_2415_);
v___f_2417_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2417_, 0, v_toSeqRight_2408_);
v___f_2418_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2418_, 0, v_toSeqLeft_2407_);
v___f_2419_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2419_, 0, v_toSeq_2406_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v___f_2417_);
lean_ctor_set(v___x_2410_, 3, v___f_2418_);
lean_ctor_set(v___x_2410_, 2, v___f_2419_);
lean_ctor_set(v___x_2410_, 1, v___f_2412_);
lean_ctor_set(v___x_2410_, 0, v___x_2416_);
v___x_2421_ = v___x_2410_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v___f_2412_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v___f_2419_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v___f_2418_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v___f_2417_);
v___x_2421_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v___f_2413_);
lean_ctor_set(v___x_2403_, 0, v___x_2421_);
v___x_2423_ = v___x_2403_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___f_2413_);
v___x_2423_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_12627__overap_2428_; lean_object* v___x_2429_; 
v___x_2424_ = l_ReaderT_instMonad___redArg(v___x_2423_);
v___x_2425_ = l_StateRefT_x27_instMonad___redArg(v___x_2424_);
v___x_2426_ = lean_box(0);
v___x_2427_ = l_instInhabitedOfMonad___redArg(v___x_2425_, v___x_2426_);
v___x_12627__overap_2428_ = lean_panic_fn_borrowed(v___x_2427_, v_msg_2367_);
lean_dec(v___x_2427_);
lean_inc(v___y_2373_);
lean_inc_ref(v___y_2372_);
lean_inc(v___y_2371_);
lean_inc_ref(v___y_2370_);
lean_inc(v___y_2369_);
lean_inc(v___y_2368_);
v___x_2429_ = lean_apply_7(v___x_12627__overap_2428_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, lean_box(0));
return v___x_2429_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec(v___y_2443_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2451_, lean_object* v_e_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_ty_2461_; lean_object* v_body_2462_; uint8_t v___x_2465_; 
v___x_2465_ = l_Lean_Expr_hasFVar(v_e_2452_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec_ref(v_e_2452_);
lean_dec_ref(v_f_2451_);
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
else
{
switch(lean_obj_tag(v_e_2452_))
{
case 1:
{
lean_object* v_fvarId_2468_; lean_object* v___x_2469_; 
v_fvarId_2468_ = lean_ctor_get(v_e_2452_, 0);
lean_inc(v_fvarId_2468_);
lean_dec_ref(v_e_2452_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
lean_inc(v___y_2454_);
lean_inc(v___y_2453_);
v___x_2469_ = lean_apply_8(v_f_2451_, v_fvarId_2468_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, lean_box(0));
return v___x_2469_;
}
case 2:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec_ref(v_e_2452_);
lean_dec_ref(v_f_2451_);
v___x_2470_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2471_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2470_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2471_;
}
case 5:
{
lean_object* v_fn_2472_; lean_object* v_arg_2473_; lean_object* v___x_2474_; 
v_fn_2472_ = lean_ctor_get(v_e_2452_, 0);
lean_inc_ref(v_fn_2472_);
v_arg_2473_ = lean_ctor_get(v_e_2452_, 1);
lean_inc_ref(v_arg_2473_);
lean_dec_ref(v_e_2452_);
lean_inc_ref(v_f_2451_);
v___x_2474_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2451_, v_fn_2472_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_dec_ref(v___x_2474_);
v_e_2452_ = v_arg_2473_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2473_);
lean_dec_ref(v_f_2451_);
return v___x_2474_;
}
}
case 6:
{
lean_object* v_binderType_2476_; lean_object* v_body_2477_; 
v_binderType_2476_ = lean_ctor_get(v_e_2452_, 1);
lean_inc_ref(v_binderType_2476_);
v_body_2477_ = lean_ctor_get(v_e_2452_, 2);
lean_inc_ref(v_body_2477_);
lean_dec_ref(v_e_2452_);
v_ty_2461_ = v_binderType_2476_;
v_body_2462_ = v_body_2477_;
goto v___jp_2460_;
}
case 7:
{
lean_object* v_binderType_2478_; lean_object* v_body_2479_; 
v_binderType_2478_ = lean_ctor_get(v_e_2452_, 1);
lean_inc_ref(v_binderType_2478_);
v_body_2479_ = lean_ctor_get(v_e_2452_, 2);
lean_inc_ref(v_body_2479_);
lean_dec_ref(v_e_2452_);
v_ty_2461_ = v_binderType_2478_;
v_body_2462_ = v_body_2479_;
goto v___jp_2460_;
}
case 8:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref(v_e_2452_);
lean_dec_ref(v_f_2451_);
v___x_2480_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2481_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2480_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2481_;
}
case 11:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref(v_e_2452_);
lean_dec_ref(v_f_2451_);
v___x_2482_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2483_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2482_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2483_;
}
default: 
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref(v_e_2452_);
lean_dec_ref(v_f_2451_);
v___x_2484_ = lean_box(0);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
}
v___jp_2460_:
{
lean_object* v___x_2463_; 
lean_inc_ref(v_f_2451_);
v___x_2463_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2451_, v_ty_2461_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_dec_ref(v___x_2463_);
v_e_2452_ = v_body_2462_;
goto _start;
}
else
{
lean_dec_ref(v_body_2462_);
lean_dec_ref(v_f_2451_);
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2486_, lean_object* v_e_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2486_, v_e_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec(v___y_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2496_, lean_object* v_arg_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
switch(lean_obj_tag(v_arg_2497_))
{
case 0:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_f_2496_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
case 1:
{
lean_object* v_fvarId_2507_; lean_object* v___x_2508_; 
v_fvarId_2507_ = lean_ctor_get(v_arg_2497_, 0);
lean_inc(v_fvarId_2507_);
lean_dec_ref(v_arg_2497_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___y_2499_);
lean_inc(v___y_2498_);
v___x_2508_ = lean_apply_8(v_f_2496_, v_fvarId_2507_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, lean_box(0));
return v___x_2508_;
}
default: 
{
lean_object* v_expr_2509_; lean_object* v___x_2510_; 
v_expr_2509_ = lean_ctor_get(v_arg_2497_, 0);
lean_inc_ref(v_expr_2509_);
lean_dec_ref(v_arg_2497_);
v___x_2510_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2496_, v_expr_2509_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2511_, lean_object* v_arg_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2511_, v_arg_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2521_, lean_object* v_param_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_type_2530_; lean_object* v___x_2531_; 
v_type_2530_ = lean_ctor_get(v_param_2522_, 2);
lean_inc_ref(v_type_2530_);
lean_dec_ref(v_param_2522_);
v___x_2531_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2521_, v_type_2530_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2532_, lean_object* v_param_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2532_, v_param_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec(v___y_2534_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2542_, lean_object* v_f_2543_, lean_object* v_as_2544_, size_t v_i_2545_, size_t v_stop_2546_, lean_object* v_b_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_usize_dec_eq(v_i_2545_, v_stop_2546_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_array_uget_borrowed(v_as_2544_, v_i_2545_);
lean_inc(v___x_2556_);
lean_inc_ref(v_f_2543_);
v___x_2557_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2543_, v___x_2556_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; size_t v___x_2559_; size_t v___x_2560_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_add(v_i_2545_, v___x_2559_);
v_i_2545_ = v___x_2560_;
v_b_2547_ = v_a_2558_;
goto _start;
}
else
{
lean_dec_ref(v_f_2543_);
return v___x_2557_;
}
}
else
{
lean_object* v___x_2562_; 
lean_dec_ref(v_f_2543_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_b_2547_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2563_, lean_object* v_f_2564_, lean_object* v_as_2565_, lean_object* v_i_2566_, lean_object* v_stop_2567_, lean_object* v_b_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v_pu_boxed_2576_; size_t v_i_boxed_2577_; size_t v_stop_boxed_2578_; lean_object* v_res_2579_; 
v_pu_boxed_2576_ = lean_unbox(v_pu_2563_);
v_i_boxed_2577_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_stop_boxed_2578_ = lean_unbox_usize(v_stop_2567_);
lean_dec(v_stop_2567_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2576_, v_f_2564_, v_as_2565_, v_i_boxed_2577_, v_stop_boxed_2578_, v_b_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v_as_2565_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2580_, lean_object* v_f_2581_, lean_object* v_as_2582_, size_t v_i_2583_, size_t v_stop_2584_, lean_object* v_b_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_eq(v_i_2583_, v_stop_2584_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_array_uget_borrowed(v_as_2582_, v_i_2583_);
lean_inc(v___x_2594_);
lean_inc_ref(v_f_2581_);
v___x_2595_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2581_, v___x_2594_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; size_t v___x_2597_; size_t v___x_2598_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_add(v_i_2583_, v___x_2597_);
v_i_2583_ = v___x_2598_;
v_b_2585_ = v_a_2596_;
goto _start;
}
else
{
lean_dec_ref(v_f_2581_);
return v___x_2595_;
}
}
else
{
lean_object* v___x_2600_; 
lean_dec_ref(v_f_2581_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_b_2585_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2601_, lean_object* v_f_2602_, lean_object* v_as_2603_, lean_object* v_i_2604_, lean_object* v_stop_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v_pu_boxed_2614_; size_t v_i_boxed_2615_; size_t v_stop_boxed_2616_; lean_object* v_res_2617_; 
v_pu_boxed_2614_ = lean_unbox(v_pu_2601_);
v_i_boxed_2615_ = lean_unbox_usize(v_i_2604_);
lean_dec(v_i_2604_);
v_stop_boxed_2616_ = lean_unbox_usize(v_stop_2605_);
lean_dec(v_stop_2605_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2614_, v_f_2602_, v_as_2603_, v_i_boxed_2615_, v_stop_boxed_2616_, v_b_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v_as_2603_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2618_, lean_object* v_f_2619_, lean_object* v_e_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_args_2629_; 
switch(lean_obj_tag(v_e_2620_))
{
case 2:
{
lean_object* v_struct_2643_; lean_object* v___x_2644_; 
v_struct_2643_ = lean_ctor_get(v_e_2620_, 2);
lean_inc(v_struct_2643_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2644_ = lean_apply_8(v_f_2619_, v_struct_2643_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2644_;
}
case 3:
{
lean_object* v_args_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_args_2645_ = lean_ctor_get(v_e_2620_, 2);
lean_inc_ref(v_args_2645_);
lean_dec_ref(v_e_2620_);
v___x_2646_ = lean_unsigned_to_nat(0u);
v___x_2647_ = lean_array_get_size(v_args_2645_);
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_nat_dec_lt(v___x_2646_, v___x_2647_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref(v_args_2645_);
lean_dec_ref(v_f_2619_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
return v___x_2650_;
}
else
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_nat_dec_le(v___x_2647_, v___x_2647_);
if (v___x_2651_ == 0)
{
if (v___x_2649_ == 0)
{
lean_object* v___x_2652_; 
lean_dec_ref(v_args_2645_);
lean_dec_ref(v_f_2619_);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2648_);
return v___x_2652_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2647_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2645_, v___x_2653_, v___x_2654_, v___x_2648_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2645_);
return v___x_2655_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2647_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2645_, v___x_2656_, v___x_2657_, v___x_2648_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2645_);
return v___x_2658_;
}
}
}
case 4:
{
lean_object* v_fvarId_2659_; lean_object* v_args_2660_; lean_object* v___x_2661_; 
v_fvarId_2659_ = lean_ctor_get(v_e_2620_, 0);
lean_inc(v_fvarId_2659_);
v_args_2660_ = lean_ctor_get(v_e_2620_, 1);
lean_inc_ref(v_args_2660_);
lean_dec_ref(v_e_2620_);
lean_inc_ref(v_f_2619_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2661_ = lean_apply_8(v_f_2619_, v_fvarId_2659_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2682_; 
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v___x_2661_, 0);
lean_dec(v_unused_2683_);
v___x_2663_ = v___x_2661_;
v_isShared_2664_ = v_isSharedCheck_2682_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v___x_2661_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2682_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v_args_2660_);
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref(v_args_2660_);
lean_dec_ref(v_f_2619_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2667_);
v___x_2670_ = v___x_2663_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2667_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
else
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2672_ == 0)
{
if (v___x_2668_ == 0)
{
lean_object* v___x_2674_; 
lean_dec_ref(v_args_2660_);
lean_dec_ref(v_f_2619_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2667_);
v___x_2674_ = v___x_2663_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2667_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
lean_del_object(v___x_2663_);
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = lean_usize_of_nat(v___x_2666_);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2660_, v___x_2676_, v___x_2677_, v___x_2667_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2660_);
return v___x_2678_;
}
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
lean_del_object(v___x_2663_);
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2666_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2660_, v___x_2679_, v___x_2680_, v___x_2667_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2660_);
return v___x_2681_;
}
}
}
}
else
{
lean_dec_ref(v_args_2660_);
lean_dec_ref(v_f_2619_);
return v___x_2661_;
}
}
case 5:
{
lean_object* v_args_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v_args_2684_ = lean_ctor_get(v_e_2620_, 1);
lean_inc_ref(v_args_2684_);
lean_dec_ref(v_e_2620_);
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = lean_array_get_size(v_args_2684_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; 
lean_dec_ref(v_args_2684_);
lean_dec_ref(v_f_2619_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
return v___x_2689_;
}
else
{
uint8_t v___x_2690_; 
v___x_2690_ = lean_nat_dec_le(v___x_2686_, v___x_2686_);
if (v___x_2690_ == 0)
{
if (v___x_2688_ == 0)
{
lean_object* v___x_2691_; 
lean_dec_ref(v_args_2684_);
lean_dec_ref(v_f_2619_);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2687_);
return v___x_2691_;
}
else
{
size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = lean_usize_of_nat(v___x_2686_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2684_, v___x_2692_, v___x_2693_, v___x_2687_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2684_);
return v___x_2694_;
}
}
else
{
size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = lean_usize_of_nat(v___x_2686_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2684_, v___x_2695_, v___x_2696_, v___x_2687_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2684_);
return v___x_2697_;
}
}
}
case 6:
{
lean_object* v_var_2698_; lean_object* v___x_2699_; 
v_var_2698_ = lean_ctor_get(v_e_2620_, 1);
lean_inc(v_var_2698_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2699_ = lean_apply_8(v_f_2619_, v_var_2698_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2699_;
}
case 7:
{
lean_object* v_var_2700_; lean_object* v___x_2701_; 
v_var_2700_ = lean_ctor_get(v_e_2620_, 1);
lean_inc(v_var_2700_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2701_ = lean_apply_8(v_f_2619_, v_var_2700_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2701_;
}
case 8:
{
lean_object* v_var_2702_; lean_object* v___x_2703_; 
v_var_2702_ = lean_ctor_get(v_e_2620_, 2);
lean_inc(v_var_2702_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2703_ = lean_apply_8(v_f_2619_, v_var_2702_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2703_;
}
case 9:
{
lean_object* v_args_2704_; 
v_args_2704_ = lean_ctor_get(v_e_2620_, 1);
lean_inc_ref(v_args_2704_);
lean_dec_ref(v_e_2620_);
v_args_2629_ = v_args_2704_;
goto v___jp_2628_;
}
case 10:
{
lean_object* v_args_2705_; 
v_args_2705_ = lean_ctor_get(v_e_2620_, 1);
lean_inc_ref(v_args_2705_);
lean_dec_ref(v_e_2620_);
v_args_2629_ = v_args_2705_;
goto v___jp_2628_;
}
case 11:
{
lean_object* v_var_2706_; lean_object* v___x_2707_; 
v_var_2706_ = lean_ctor_get(v_e_2620_, 1);
lean_inc(v_var_2706_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2707_ = lean_apply_8(v_f_2619_, v_var_2706_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2707_;
}
case 12:
{
lean_object* v_var_2708_; lean_object* v_args_2709_; lean_object* v___x_2710_; 
v_var_2708_ = lean_ctor_get(v_e_2620_, 0);
lean_inc(v_var_2708_);
v_args_2709_ = lean_ctor_get(v_e_2620_, 2);
lean_inc_ref(v_args_2709_);
lean_dec_ref(v_e_2620_);
lean_inc_ref(v_f_2619_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2710_ = lean_apply_8(v_f_2619_, v_var_2708_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2731_; 
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v___x_2710_, 0);
lean_dec(v_unused_2732_);
v___x_2712_ = v___x_2710_;
v_isShared_2713_ = v_isSharedCheck_2731_;
goto v_resetjp_2711_;
}
else
{
lean_dec(v___x_2710_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2731_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2714_ = lean_unsigned_to_nat(0u);
v___x_2715_ = lean_array_get_size(v_args_2709_);
v___x_2716_ = lean_box(0);
v___x_2717_ = lean_nat_dec_lt(v___x_2714_, v___x_2715_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2719_; 
lean_dec_ref(v_args_2709_);
lean_dec_ref(v_f_2619_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2716_);
v___x_2719_ = v___x_2712_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2716_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
else
{
uint8_t v___x_2721_; 
v___x_2721_ = lean_nat_dec_le(v___x_2715_, v___x_2715_);
if (v___x_2721_ == 0)
{
if (v___x_2717_ == 0)
{
lean_object* v___x_2723_; 
lean_dec_ref(v_args_2709_);
lean_dec_ref(v_f_2619_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2716_);
v___x_2723_ = v___x_2712_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2716_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
else
{
size_t v___x_2725_; size_t v___x_2726_; lean_object* v___x_2727_; 
lean_del_object(v___x_2712_);
v___x_2725_ = ((size_t)0ULL);
v___x_2726_ = lean_usize_of_nat(v___x_2715_);
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2709_, v___x_2725_, v___x_2726_, v___x_2716_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2709_);
return v___x_2727_;
}
}
else
{
size_t v___x_2728_; size_t v___x_2729_; lean_object* v___x_2730_; 
lean_del_object(v___x_2712_);
v___x_2728_ = ((size_t)0ULL);
v___x_2729_ = lean_usize_of_nat(v___x_2715_);
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2709_, v___x_2728_, v___x_2729_, v___x_2716_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2709_);
return v___x_2730_;
}
}
}
}
else
{
lean_dec_ref(v_args_2709_);
lean_dec_ref(v_f_2619_);
return v___x_2710_;
}
}
case 13:
{
lean_object* v_fvarId_2733_; lean_object* v___x_2734_; 
v_fvarId_2733_ = lean_ctor_get(v_e_2620_, 1);
lean_inc(v_fvarId_2733_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2734_ = lean_apply_8(v_f_2619_, v_fvarId_2733_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2734_;
}
case 14:
{
lean_object* v_fvarId_2735_; lean_object* v___x_2736_; 
v_fvarId_2735_ = lean_ctor_get(v_e_2620_, 0);
lean_inc(v_fvarId_2735_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2736_ = lean_apply_8(v_f_2619_, v_fvarId_2735_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2736_;
}
case 15:
{
lean_object* v_fvarId_2737_; lean_object* v___x_2738_; 
v_fvarId_2737_ = lean_ctor_get(v_e_2620_, 0);
lean_inc(v_fvarId_2737_);
lean_dec_ref(v_e_2620_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc(v___y_2621_);
v___x_2738_ = lean_apply_8(v_f_2619_, v_fvarId_2737_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2738_;
}
default: 
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec(v_e_2620_);
lean_dec_ref(v_f_2619_);
v___x_2739_ = lean_box(0);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
return v___x_2740_;
}
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2630_ = lean_unsigned_to_nat(0u);
v___x_2631_ = lean_array_get_size(v_args_2629_);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_nat_dec_lt(v___x_2630_, v___x_2631_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec_ref(v_args_2629_);
lean_dec_ref(v_f_2619_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
return v___x_2634_;
}
else
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_nat_dec_le(v___x_2631_, v___x_2631_);
if (v___x_2635_ == 0)
{
if (v___x_2633_ == 0)
{
lean_object* v___x_2636_; 
lean_dec_ref(v_args_2629_);
lean_dec_ref(v_f_2619_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2632_);
return v___x_2636_;
}
else
{
size_t v___x_2637_; size_t v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((size_t)0ULL);
v___x_2638_ = lean_usize_of_nat(v___x_2631_);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2629_, v___x_2637_, v___x_2638_, v___x_2632_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2629_);
return v___x_2639_;
}
}
else
{
size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2631_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2618_, v_f_2619_, v_args_2629_, v___x_2640_, v___x_2641_, v___x_2632_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec_ref(v_args_2629_);
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2741_, lean_object* v_f_2742_, lean_object* v_e_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
uint8_t v_pu_boxed_2751_; lean_object* v_res_2752_; 
v_pu_boxed_2751_ = lean_unbox(v_pu_2741_);
v_res_2752_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2751_, v_f_2742_, v_e_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2753_, lean_object* v_f_2754_, lean_object* v_decl_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_type_2763_; lean_object* v_value_2764_; lean_object* v___x_2765_; 
v_type_2763_ = lean_ctor_get(v_decl_2755_, 2);
lean_inc_ref(v_type_2763_);
v_value_2764_ = lean_ctor_get(v_decl_2755_, 3);
lean_inc(v_value_2764_);
lean_dec_ref(v_decl_2755_);
lean_inc_ref(v_f_2754_);
v___x_2765_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2754_, v_type_2763_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2766_; 
lean_dec_ref(v___x_2765_);
v___x_2766_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2753_, v_f_2754_, v_value_2764_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2766_;
}
else
{
lean_dec(v_value_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2767_, lean_object* v_f_2768_, lean_object* v_decl_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v_pu_boxed_2777_; lean_object* v_res_2778_; 
v_pu_boxed_2777_ = lean_unbox(v_pu_2767_);
v_res_2778_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2777_, v_f_2768_, v_decl_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec(v___y_2770_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2779_, lean_object* v_f_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
switch(lean_obj_tag(v_alt_2779_))
{
case 0:
{
lean_object* v_code_2788_; lean_object* v___x_2789_; 
v_code_2788_ = lean_ctor_get(v_alt_2779_, 2);
lean_inc_ref(v_code_2788_);
lean_dec_ref(v_alt_2779_);
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc(v___y_2781_);
v___x_2789_ = lean_apply_8(v_f_2780_, v_code_2788_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, lean_box(0));
return v___x_2789_;
}
case 1:
{
lean_object* v_code_2790_; lean_object* v___x_2791_; 
v_code_2790_ = lean_ctor_get(v_alt_2779_, 1);
lean_inc_ref(v_code_2790_);
lean_dec_ref(v_alt_2779_);
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc(v___y_2781_);
v___x_2791_ = lean_apply_8(v_f_2780_, v_code_2790_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, lean_box(0));
return v___x_2791_;
}
default: 
{
lean_object* v_code_2792_; lean_object* v___x_2793_; 
v_code_2792_ = lean_ctor_get(v_alt_2779_, 0);
lean_inc_ref(v_code_2792_);
lean_dec_ref(v_alt_2779_);
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc(v___y_2781_);
v___x_2793_ = lean_apply_8(v_f_2780_, v_code_2792_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, lean_box(0));
return v___x_2793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2794_, lean_object* v_f_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2794_, v_f_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2804_, lean_object* v_f_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v_pu_boxed_2814_; lean_object* v_res_2815_; 
v_pu_boxed_2814_ = lean_unbox(v_pu_2804_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2814_, v_f_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2816_, lean_object* v_f_2817_, lean_object* v_as_2818_, size_t v_i_2819_, size_t v_stop_2820_, lean_object* v_b_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
uint8_t v___x_2829_; 
v___x_2829_ = lean_usize_dec_eq(v_i_2819_, v_stop_2820_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2830_ = lean_box(v_pu_2816_);
lean_inc_ref(v_f_2817_);
v___f_2831_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2831_, 0, v___x_2830_);
lean_closure_set(v___f_2831_, 1, v_f_2817_);
v___x_2832_ = lean_array_uget_borrowed(v_as_2818_, v_i_2819_);
lean_inc(v___x_2832_);
v___x_2833_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2832_, v___f_2831_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; size_t v___x_2835_; size_t v___x_2836_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref(v___x_2833_);
v___x_2835_ = ((size_t)1ULL);
v___x_2836_ = lean_usize_add(v_i_2819_, v___x_2835_);
v_i_2819_ = v___x_2836_;
v_b_2821_ = v_a_2834_;
goto _start;
}
else
{
lean_dec_ref(v_f_2817_);
return v___x_2833_;
}
}
else
{
lean_object* v___x_2838_; 
lean_dec_ref(v_f_2817_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_b_2821_);
return v___x_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2839_, lean_object* v_f_2840_, lean_object* v_c_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
switch(lean_obj_tag(v_c_2841_))
{
case 0:
{
lean_object* v_decl_2849_; lean_object* v_k_2850_; lean_object* v___x_2851_; 
v_decl_2849_ = lean_ctor_get(v_c_2841_, 0);
lean_inc_ref(v_decl_2849_);
v_k_2850_ = lean_ctor_get(v_c_2841_, 1);
lean_inc_ref(v_k_2850_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
v___x_2851_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2839_, v_f_2840_, v_decl_2849_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_dec_ref(v___x_2851_);
v_c_2841_ = v_k_2850_;
goto _start;
}
else
{
lean_dec_ref(v_k_2850_);
lean_dec_ref(v_f_2840_);
return v___x_2851_;
}
}
case 1:
{
lean_object* v_decl_2853_; lean_object* v_k_2854_; lean_object* v_params_2855_; lean_object* v_type_2856_; lean_object* v_value_2857_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v_decl_2853_ = lean_ctor_get(v_c_2841_, 0);
lean_inc_ref(v_decl_2853_);
v_k_2854_ = lean_ctor_get(v_c_2841_, 1);
lean_inc_ref(v_k_2854_);
lean_dec_ref(v_c_2841_);
v_params_2855_ = lean_ctor_get(v_decl_2853_, 2);
lean_inc_ref(v_params_2855_);
v_type_2856_ = lean_ctor_get(v_decl_2853_, 3);
lean_inc_ref(v_type_2856_);
v_value_2857_ = lean_ctor_get(v_decl_2853_, 4);
lean_inc_ref(v_value_2857_);
lean_dec_ref(v_decl_2853_);
v___x_2868_ = lean_unsigned_to_nat(0u);
v___x_2869_ = lean_array_get_size(v_params_2855_);
v___x_2870_ = lean_nat_dec_lt(v___x_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
lean_dec_ref(v_params_2855_);
lean_inc_ref(v_f_2840_);
v___x_2871_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_type_2856_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref(v___x_2871_);
lean_inc_ref(v_f_2840_);
v___x_2872_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2839_, v_f_2840_, v_value_2857_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_dec_ref(v___x_2872_);
v_c_2841_ = v_k_2854_;
goto _start;
}
else
{
lean_dec_ref(v_k_2854_);
lean_dec_ref(v_f_2840_);
return v___x_2872_;
}
}
else
{
lean_dec_ref(v_value_2857_);
lean_dec_ref(v_k_2854_);
lean_dec_ref(v_f_2840_);
return v___x_2871_;
}
}
else
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = lean_box(0);
v___x_2875_ = lean_nat_dec_le(v___x_2869_, v___x_2869_);
if (v___x_2875_ == 0)
{
if (v___x_2870_ == 0)
{
lean_dec_ref(v_params_2855_);
v___y_2859_ = v___y_2842_;
v___y_2860_ = v___y_2843_;
v___y_2861_ = v___y_2844_;
v___y_2862_ = v___y_2845_;
v___y_2863_ = v___y_2846_;
v___y_2864_ = v___y_2847_;
goto v___jp_2858_;
}
else
{
size_t v___x_2876_; size_t v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = lean_usize_of_nat(v___x_2869_);
lean_inc_ref(v_f_2840_);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2839_, v_f_2840_, v_params_2855_, v___x_2876_, v___x_2877_, v___x_2874_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_params_2855_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_dec_ref(v___x_2878_);
v___y_2859_ = v___y_2842_;
v___y_2860_ = v___y_2843_;
v___y_2861_ = v___y_2844_;
v___y_2862_ = v___y_2845_;
v___y_2863_ = v___y_2846_;
v___y_2864_ = v___y_2847_;
goto v___jp_2858_;
}
else
{
lean_dec_ref(v_value_2857_);
lean_dec_ref(v_type_2856_);
lean_dec_ref(v_k_2854_);
lean_dec_ref(v_f_2840_);
return v___x_2878_;
}
}
}
else
{
size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = lean_usize_of_nat(v___x_2869_);
lean_inc_ref(v_f_2840_);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2839_, v_f_2840_, v_params_2855_, v___x_2879_, v___x_2880_, v___x_2874_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_params_2855_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_dec_ref(v___x_2881_);
v___y_2859_ = v___y_2842_;
v___y_2860_ = v___y_2843_;
v___y_2861_ = v___y_2844_;
v___y_2862_ = v___y_2845_;
v___y_2863_ = v___y_2846_;
v___y_2864_ = v___y_2847_;
goto v___jp_2858_;
}
else
{
lean_dec_ref(v_value_2857_);
lean_dec_ref(v_type_2856_);
lean_dec_ref(v_k_2854_);
lean_dec_ref(v_f_2840_);
return v___x_2881_;
}
}
}
v___jp_2858_:
{
lean_object* v___x_2865_; 
lean_inc_ref(v_f_2840_);
v___x_2865_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_type_2856_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v___x_2866_; 
lean_dec_ref(v___x_2865_);
lean_inc_ref(v_f_2840_);
v___x_2866_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2839_, v_f_2840_, v_value_2857_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_dec_ref(v___x_2866_);
v_c_2841_ = v_k_2854_;
v___y_2842_ = v___y_2859_;
v___y_2843_ = v___y_2860_;
v___y_2844_ = v___y_2861_;
v___y_2845_ = v___y_2862_;
v___y_2846_ = v___y_2863_;
v___y_2847_ = v___y_2864_;
goto _start;
}
else
{
lean_dec_ref(v_k_2854_);
lean_dec_ref(v_f_2840_);
return v___x_2866_;
}
}
else
{
lean_dec_ref(v_value_2857_);
lean_dec_ref(v_k_2854_);
lean_dec_ref(v_f_2840_);
return v___x_2865_;
}
}
}
case 2:
{
lean_object* v_decl_2882_; lean_object* v_k_2883_; lean_object* v_params_2884_; lean_object* v_type_2885_; lean_object* v_value_2886_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_decl_2882_ = lean_ctor_get(v_c_2841_, 0);
lean_inc_ref(v_decl_2882_);
v_k_2883_ = lean_ctor_get(v_c_2841_, 1);
lean_inc_ref(v_k_2883_);
lean_dec_ref(v_c_2841_);
v_params_2884_ = lean_ctor_get(v_decl_2882_, 2);
lean_inc_ref(v_params_2884_);
v_type_2885_ = lean_ctor_get(v_decl_2882_, 3);
lean_inc_ref(v_type_2885_);
v_value_2886_ = lean_ctor_get(v_decl_2882_, 4);
lean_inc_ref(v_value_2886_);
lean_dec_ref(v_decl_2882_);
v___x_2897_ = lean_unsigned_to_nat(0u);
v___x_2898_ = lean_array_get_size(v_params_2884_);
v___x_2899_ = lean_nat_dec_lt(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_dec_ref(v_params_2884_);
lean_inc_ref(v_f_2840_);
v___x_2900_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_type_2885_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v___x_2901_; 
lean_dec_ref(v___x_2900_);
lean_inc_ref(v_f_2840_);
v___x_2901_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2839_, v_f_2840_, v_value_2886_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_dec_ref(v___x_2901_);
v_c_2841_ = v_k_2883_;
goto _start;
}
else
{
lean_dec_ref(v_k_2883_);
lean_dec_ref(v_f_2840_);
return v___x_2901_;
}
}
else
{
lean_dec_ref(v_value_2886_);
lean_dec_ref(v_k_2883_);
lean_dec_ref(v_f_2840_);
return v___x_2900_;
}
}
else
{
lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = lean_box(0);
v___x_2904_ = lean_nat_dec_le(v___x_2898_, v___x_2898_);
if (v___x_2904_ == 0)
{
if (v___x_2899_ == 0)
{
lean_dec_ref(v_params_2884_);
v___y_2888_ = v___y_2842_;
v___y_2889_ = v___y_2843_;
v___y_2890_ = v___y_2844_;
v___y_2891_ = v___y_2845_;
v___y_2892_ = v___y_2846_;
v___y_2893_ = v___y_2847_;
goto v___jp_2887_;
}
else
{
size_t v___x_2905_; size_t v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = ((size_t)0ULL);
v___x_2906_ = lean_usize_of_nat(v___x_2898_);
lean_inc_ref(v_f_2840_);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2839_, v_f_2840_, v_params_2884_, v___x_2905_, v___x_2906_, v___x_2903_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_params_2884_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_dec_ref(v___x_2907_);
v___y_2888_ = v___y_2842_;
v___y_2889_ = v___y_2843_;
v___y_2890_ = v___y_2844_;
v___y_2891_ = v___y_2845_;
v___y_2892_ = v___y_2846_;
v___y_2893_ = v___y_2847_;
goto v___jp_2887_;
}
else
{
lean_dec_ref(v_value_2886_);
lean_dec_ref(v_type_2885_);
lean_dec_ref(v_k_2883_);
lean_dec_ref(v_f_2840_);
return v___x_2907_;
}
}
}
else
{
size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_of_nat(v___x_2898_);
lean_inc_ref(v_f_2840_);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2839_, v_f_2840_, v_params_2884_, v___x_2908_, v___x_2909_, v___x_2903_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_params_2884_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_dec_ref(v___x_2910_);
v___y_2888_ = v___y_2842_;
v___y_2889_ = v___y_2843_;
v___y_2890_ = v___y_2844_;
v___y_2891_ = v___y_2845_;
v___y_2892_ = v___y_2846_;
v___y_2893_ = v___y_2847_;
goto v___jp_2887_;
}
else
{
lean_dec_ref(v_value_2886_);
lean_dec_ref(v_type_2885_);
lean_dec_ref(v_k_2883_);
lean_dec_ref(v_f_2840_);
return v___x_2910_;
}
}
}
v___jp_2887_:
{
lean_object* v___x_2894_; 
lean_inc_ref(v_f_2840_);
v___x_2894_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_type_2885_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; 
lean_dec_ref(v___x_2894_);
lean_inc_ref(v_f_2840_);
v___x_2895_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2839_, v_f_2840_, v_value_2886_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_dec_ref(v___x_2895_);
v_c_2841_ = v_k_2883_;
v___y_2842_ = v___y_2888_;
v___y_2843_ = v___y_2889_;
v___y_2844_ = v___y_2890_;
v___y_2845_ = v___y_2891_;
v___y_2846_ = v___y_2892_;
v___y_2847_ = v___y_2893_;
goto _start;
}
else
{
lean_dec_ref(v_k_2883_);
lean_dec_ref(v_f_2840_);
return v___x_2895_;
}
}
else
{
lean_dec_ref(v_value_2886_);
lean_dec_ref(v_k_2883_);
lean_dec_ref(v_f_2840_);
return v___x_2894_;
}
}
}
case 3:
{
lean_object* v_fvarId_2911_; lean_object* v_args_2912_; lean_object* v___x_2913_; 
v_fvarId_2911_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2911_);
v_args_2912_ = lean_ctor_get(v_c_2841_, 1);
lean_inc_ref(v_args_2912_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2913_ = lean_apply_8(v_f_2840_, v_fvarId_2911_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2934_; 
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2934_ == 0)
{
lean_object* v_unused_2935_; 
v_unused_2935_ = lean_ctor_get(v___x_2913_, 0);
lean_dec(v_unused_2935_);
v___x_2915_ = v___x_2913_;
v_isShared_2916_ = v_isSharedCheck_2934_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v___x_2913_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2934_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = lean_array_get_size(v_args_2912_);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_nat_dec_lt(v___x_2917_, v___x_2918_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2922_; 
lean_dec_ref(v_args_2912_);
lean_dec_ref(v_f_2840_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2919_);
v___x_2922_ = v___x_2915_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2919_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
else
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_nat_dec_le(v___x_2918_, v___x_2918_);
if (v___x_2924_ == 0)
{
if (v___x_2920_ == 0)
{
lean_object* v___x_2926_; 
lean_dec_ref(v_args_2912_);
lean_dec_ref(v_f_2840_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2919_);
v___x_2926_ = v___x_2915_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2919_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
else
{
size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
lean_del_object(v___x_2915_);
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = lean_usize_of_nat(v___x_2918_);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2839_, v_f_2840_, v_args_2912_, v___x_2928_, v___x_2929_, v___x_2919_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_args_2912_);
return v___x_2930_;
}
}
else
{
size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
lean_del_object(v___x_2915_);
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2918_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2839_, v_f_2840_, v_args_2912_, v___x_2931_, v___x_2932_, v___x_2919_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_args_2912_);
return v___x_2933_;
}
}
}
}
else
{
lean_dec_ref(v_args_2912_);
lean_dec_ref(v_f_2840_);
return v___x_2913_;
}
}
case 4:
{
lean_object* v_cases_2936_; lean_object* v_resultType_2937_; lean_object* v_discr_2938_; lean_object* v_alts_2939_; lean_object* v___x_2940_; 
v_cases_2936_ = lean_ctor_get(v_c_2841_, 0);
lean_inc_ref(v_cases_2936_);
lean_dec_ref(v_c_2841_);
v_resultType_2937_ = lean_ctor_get(v_cases_2936_, 1);
lean_inc_ref(v_resultType_2937_);
v_discr_2938_ = lean_ctor_get(v_cases_2936_, 2);
lean_inc(v_discr_2938_);
v_alts_2939_ = lean_ctor_get(v_cases_2936_, 3);
lean_inc_ref(v_alts_2939_);
lean_dec_ref(v_cases_2936_);
lean_inc_ref(v_f_2840_);
v___x_2940_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_resultType_2937_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2941_; 
lean_dec_ref(v___x_2940_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2941_ = lean_apply_8(v_f_2840_, v_discr_2938_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2962_; 
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v___x_2941_, 0);
lean_dec(v_unused_2963_);
v___x_2943_ = v___x_2941_;
v_isShared_2944_ = v_isSharedCheck_2962_;
goto v_resetjp_2942_;
}
else
{
lean_dec(v___x_2941_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2962_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = lean_array_get_size(v_alts_2939_);
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_nat_dec_lt(v___x_2945_, v___x_2946_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2950_; 
lean_dec_ref(v_alts_2939_);
lean_dec_ref(v_f_2840_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2947_);
v___x_2950_ = v___x_2943_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2947_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
else
{
uint8_t v___x_2952_; 
v___x_2952_ = lean_nat_dec_le(v___x_2946_, v___x_2946_);
if (v___x_2952_ == 0)
{
if (v___x_2948_ == 0)
{
lean_object* v___x_2954_; 
lean_dec_ref(v_alts_2939_);
lean_dec_ref(v_f_2840_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2947_);
v___x_2954_ = v___x_2943_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2947_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
else
{
size_t v___x_2956_; size_t v___x_2957_; lean_object* v___x_2958_; 
lean_del_object(v___x_2943_);
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = lean_usize_of_nat(v___x_2946_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2839_, v_f_2840_, v_alts_2939_, v___x_2956_, v___x_2957_, v___x_2947_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_alts_2939_);
return v___x_2958_;
}
}
else
{
size_t v___x_2959_; size_t v___x_2960_; lean_object* v___x_2961_; 
lean_del_object(v___x_2943_);
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = lean_usize_of_nat(v___x_2946_);
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2839_, v_f_2840_, v_alts_2939_, v___x_2959_, v___x_2960_, v___x_2947_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v_alts_2939_);
return v___x_2961_;
}
}
}
}
else
{
lean_dec_ref(v_alts_2939_);
lean_dec_ref(v_f_2840_);
return v___x_2941_;
}
}
else
{
lean_dec_ref(v_alts_2939_);
lean_dec(v_discr_2938_);
lean_dec_ref(v_f_2840_);
return v___x_2940_;
}
}
case 5:
{
lean_object* v_fvarId_2964_; lean_object* v___x_2965_; 
v_fvarId_2964_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2964_);
lean_dec_ref(v_c_2841_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2965_ = lean_apply_8(v_f_2840_, v_fvarId_2964_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
return v___x_2965_;
}
case 6:
{
lean_object* v_type_2966_; lean_object* v___x_2967_; 
v_type_2966_ = lean_ctor_get(v_c_2841_, 0);
lean_inc_ref(v_type_2966_);
lean_dec_ref(v_c_2841_);
v___x_2967_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_type_2966_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2967_;
}
case 7:
{
lean_object* v_fvarId_2968_; lean_object* v_y_2969_; lean_object* v_k_2970_; lean_object* v___x_2971_; 
v_fvarId_2968_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2968_);
v_y_2969_ = lean_ctor_get(v_c_2841_, 2);
lean_inc(v_y_2969_);
v_k_2970_ = lean_ctor_get(v_c_2841_, 3);
lean_inc_ref(v_k_2970_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2971_ = lean_apply_8(v_f_2840_, v_fvarId_2968_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2972_; 
lean_dec_ref(v___x_2971_);
lean_inc_ref(v_f_2840_);
v___x_2972_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2840_, v_y_2969_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_dec_ref(v___x_2972_);
v_c_2841_ = v_k_2970_;
goto _start;
}
else
{
lean_dec_ref(v_k_2970_);
lean_dec_ref(v_f_2840_);
return v___x_2972_;
}
}
else
{
lean_dec_ref(v_k_2970_);
lean_dec(v_y_2969_);
lean_dec_ref(v_f_2840_);
return v___x_2971_;
}
}
case 8:
{
lean_object* v_fvarId_2974_; lean_object* v_y_2975_; lean_object* v_k_2976_; lean_object* v___x_2977_; 
v_fvarId_2974_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2974_);
v_y_2975_ = lean_ctor_get(v_c_2841_, 2);
lean_inc(v_y_2975_);
v_k_2976_ = lean_ctor_get(v_c_2841_, 3);
lean_inc_ref(v_k_2976_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2977_ = lean_apply_8(v_f_2840_, v_fvarId_2974_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v___x_2978_; 
lean_dec_ref(v___x_2977_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2978_ = lean_apply_8(v_f_2840_, v_y_2975_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_dec_ref(v___x_2978_);
v_c_2841_ = v_k_2976_;
goto _start;
}
else
{
lean_dec_ref(v_k_2976_);
lean_dec_ref(v_f_2840_);
return v___x_2978_;
}
}
else
{
lean_dec_ref(v_k_2976_);
lean_dec(v_y_2975_);
lean_dec_ref(v_f_2840_);
return v___x_2977_;
}
}
case 9:
{
lean_object* v_fvarId_2980_; lean_object* v_y_2981_; lean_object* v_ty_2982_; lean_object* v_k_2983_; lean_object* v___x_2984_; 
v_fvarId_2980_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2980_);
v_y_2981_ = lean_ctor_get(v_c_2841_, 3);
lean_inc(v_y_2981_);
v_ty_2982_ = lean_ctor_get(v_c_2841_, 4);
lean_inc_ref(v_ty_2982_);
v_k_2983_ = lean_ctor_get(v_c_2841_, 5);
lean_inc_ref(v_k_2983_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2984_ = lean_apply_8(v_f_2840_, v_fvarId_2980_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2985_; 
lean_dec_ref(v___x_2984_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2985_ = lean_apply_8(v_f_2840_, v_y_2981_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref(v___x_2985_);
lean_inc_ref(v_f_2840_);
v___x_2986_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2840_, v_ty_2982_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_dec_ref(v___x_2986_);
v_c_2841_ = v_k_2983_;
goto _start;
}
else
{
lean_dec_ref(v_k_2983_);
lean_dec_ref(v_f_2840_);
return v___x_2986_;
}
}
else
{
lean_dec_ref(v_k_2983_);
lean_dec_ref(v_ty_2982_);
lean_dec_ref(v_f_2840_);
return v___x_2985_;
}
}
else
{
lean_dec_ref(v_k_2983_);
lean_dec_ref(v_ty_2982_);
lean_dec(v_y_2981_);
lean_dec_ref(v_f_2840_);
return v___x_2984_;
}
}
case 13:
{
lean_object* v_fvarId_2988_; lean_object* v_k_2989_; lean_object* v___x_2990_; 
v_fvarId_2988_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2988_);
v_k_2989_ = lean_ctor_get(v_c_2841_, 1);
lean_inc_ref(v_k_2989_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2990_ = lean_apply_8(v_f_2840_, v_fvarId_2988_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_dec_ref(v___x_2990_);
v_c_2841_ = v_k_2989_;
goto _start;
}
else
{
lean_dec_ref(v_k_2989_);
lean_dec_ref(v_f_2840_);
return v___x_2990_;
}
}
default: 
{
lean_object* v_fvarId_2992_; lean_object* v_k_2993_; lean_object* v___x_2994_; 
v_fvarId_2992_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_fvarId_2992_);
v_k_2993_ = lean_ctor_get(v_c_2841_, 2);
lean_inc_ref(v_k_2993_);
lean_dec_ref(v_c_2841_);
lean_inc_ref(v_f_2840_);
lean_inc(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc(v___y_2842_);
v___x_2994_ = lean_apply_8(v_f_2840_, v_fvarId_2992_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, lean_box(0));
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_dec_ref(v___x_2994_);
v_c_2841_ = v_k_2993_;
goto _start;
}
else
{
lean_dec_ref(v_k_2993_);
lean_dec_ref(v_f_2840_);
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2996_, lean_object* v_f_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2996_, v_f_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_3007_, lean_object* v_f_3008_, lean_object* v_as_3009_, lean_object* v_i_3010_, lean_object* v_stop_3011_, lean_object* v_b_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
uint8_t v_pu_boxed_3020_; size_t v_i_boxed_3021_; size_t v_stop_boxed_3022_; lean_object* v_res_3023_; 
v_pu_boxed_3020_ = lean_unbox(v_pu_3007_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3010_);
lean_dec(v_i_3010_);
v_stop_boxed_3022_ = lean_unbox_usize(v_stop_3011_);
lean_dec(v_stop_3011_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_3020_, v_f_3008_, v_as_3009_, v_i_boxed_3021_, v_stop_boxed_3022_, v_b_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v_as_3009_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_3024_, lean_object* v_f_3025_, lean_object* v_c_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
uint8_t v_pu_boxed_3034_; lean_object* v_res_3035_; 
v_pu_boxed_3034_ = lean_unbox(v_pu_3024_);
v_res_3035_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_3034_, v_f_3025_, v_c_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_3036_, lean_object* v_f_3037_, lean_object* v_decl_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_params_3046_; lean_object* v_type_3047_; lean_object* v_value_3048_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v_params_3046_ = lean_ctor_get(v_decl_3038_, 2);
lean_inc_ref(v_params_3046_);
v_type_3047_ = lean_ctor_get(v_decl_3038_, 3);
lean_inc_ref(v_type_3047_);
v_value_3048_ = lean_ctor_get(v_decl_3038_, 4);
lean_inc_ref(v_value_3048_);
lean_dec_ref(v_decl_3038_);
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_array_get_size(v_params_3046_);
v___x_3060_ = lean_nat_dec_lt(v___x_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_dec_ref(v_params_3046_);
lean_inc_ref(v_f_3037_);
v___x_3061_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3037_, v_type_3047_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; 
lean_dec_ref(v___x_3061_);
v___x_3062_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_3036_, v_f_3037_, v_value_3048_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
return v___x_3062_;
}
else
{
lean_dec_ref(v_value_3048_);
lean_dec_ref(v_f_3037_);
return v___x_3061_;
}
}
else
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_box(0);
v___x_3064_ = lean_nat_dec_le(v___x_3059_, v___x_3059_);
if (v___x_3064_ == 0)
{
if (v___x_3060_ == 0)
{
lean_dec_ref(v_params_3046_);
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
v___y_3053_ = v___y_3042_;
v___y_3054_ = v___y_3043_;
v___y_3055_ = v___y_3044_;
goto v___jp_3049_;
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = lean_usize_of_nat(v___x_3059_);
lean_inc_ref(v_f_3037_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3036_, v_f_3037_, v_params_3046_, v___x_3065_, v___x_3066_, v___x_3063_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec_ref(v_params_3046_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_dec_ref(v___x_3067_);
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
v___y_3053_ = v___y_3042_;
v___y_3054_ = v___y_3043_;
v___y_3055_ = v___y_3044_;
goto v___jp_3049_;
}
else
{
lean_dec_ref(v_value_3048_);
lean_dec_ref(v_type_3047_);
lean_dec_ref(v_f_3037_);
return v___x_3067_;
}
}
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3059_);
lean_inc_ref(v_f_3037_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_3036_, v_f_3037_, v_params_3046_, v___x_3068_, v___x_3069_, v___x_3063_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec_ref(v_params_3046_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_dec_ref(v___x_3070_);
v___y_3050_ = v___y_3039_;
v___y_3051_ = v___y_3040_;
v___y_3052_ = v___y_3041_;
v___y_3053_ = v___y_3042_;
v___y_3054_ = v___y_3043_;
v___y_3055_ = v___y_3044_;
goto v___jp_3049_;
}
else
{
lean_dec_ref(v_value_3048_);
lean_dec_ref(v_type_3047_);
lean_dec_ref(v_f_3037_);
return v___x_3070_;
}
}
}
v___jp_3049_:
{
lean_object* v___x_3056_; 
lean_inc_ref(v_f_3037_);
v___x_3056_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_3037_, v_type_3047_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; 
lean_dec_ref(v___x_3056_);
v___x_3057_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_3036_, v_f_3037_, v_value_3048_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v___x_3057_;
}
else
{
lean_dec_ref(v_value_3048_);
lean_dec_ref(v_f_3037_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_3071_, lean_object* v_f_3072_, lean_object* v_decl_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v_pu_boxed_3081_; lean_object* v_res_3082_; 
v_pu_boxed_3081_ = lean_unbox(v_pu_3071_);
v_res_3082_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_3081_, v_f_3072_, v_decl_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec(v___y_3074_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_3083_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_panic_fn_borrowed(v___x_3084_, v_msg_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3089_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_3090_ = lean_unsigned_to_nat(11u);
v___x_3091_ = lean_unsigned_to_nat(163u);
v___x_3092_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_3093_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_3094_ = l_mkPanicMessageWithDecl(v___x_3093_, v___x_3092_, v___x_3091_, v___x_3090_, v___x_3089_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_3095_, lean_object* v_x_3096_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3098_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_3097_);
return v___x_3098_;
}
else
{
lean_object* v_key_3099_; lean_object* v_value_3100_; lean_object* v_tail_3101_; uint8_t v___x_3102_; 
v_key_3099_ = lean_ctor_get(v_x_3096_, 0);
v_value_3100_ = lean_ctor_get(v_x_3096_, 1);
v_tail_3101_ = lean_ctor_get(v_x_3096_, 2);
v___x_3102_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_3099_, v_a_3095_);
if (v___x_3102_ == 0)
{
v_x_3096_ = v_tail_3101_;
goto _start;
}
else
{
lean_inc(v_value_3100_);
return v_value_3100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_3104_, lean_object* v_x_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3104_, v_x_3105_);
lean_dec(v_x_3105_);
lean_dec(v_a_3104_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_buckets_3109_; lean_object* v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v___x_3113_; uint64_t v_fold_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; uint64_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; size_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_buckets_3109_ = lean_ctor_get(v_m_3107_, 1);
v___x_3110_ = lean_array_get_size(v_buckets_3109_);
v___x_3111_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_3108_);
v___x_3112_ = 32ULL;
v___x_3113_ = lean_uint64_shift_right(v___x_3111_, v___x_3112_);
v_fold_3114_ = lean_uint64_xor(v___x_3111_, v___x_3113_);
v___x_3115_ = 16ULL;
v___x_3116_ = lean_uint64_shift_right(v_fold_3114_, v___x_3115_);
v___x_3117_ = lean_uint64_xor(v_fold_3114_, v___x_3116_);
v___x_3118_ = lean_uint64_to_usize(v___x_3117_);
v___x_3119_ = lean_usize_of_nat(v___x_3110_);
v___x_3120_ = ((size_t)1ULL);
v___x_3121_ = lean_usize_sub(v___x_3119_, v___x_3120_);
v___x_3122_ = lean_usize_land(v___x_3118_, v___x_3121_);
v___x_3123_ = lean_array_uget_borrowed(v_buckets_3109_, v___x_3122_);
v___x_3124_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3108_, v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3125_, v_a_3126_);
lean_dec(v_a_3126_);
lean_dec_ref(v_m_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___y_3138_; uint8_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = 0;
v___x_3164_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3129_))
{
case 0:
{
lean_object* v_decl_3165_; lean_object* v___x_3166_; 
v_decl_3165_ = lean_ctor_get(v_decl_3129_, 0);
lean_inc_ref(v_decl_3165_);
v___x_3166_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3163_, v___x_3164_, v_decl_3165_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
v___y_3138_ = v___x_3166_;
goto v___jp_3137_;
}
case 1:
{
lean_object* v_decl_3167_; lean_object* v___x_3168_; 
v_decl_3167_ = lean_ctor_get(v_decl_3129_, 0);
lean_inc_ref(v_decl_3167_);
v___x_3168_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3163_, v___x_3164_, v_decl_3167_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
v___y_3138_ = v___x_3168_;
goto v___jp_3137_;
}
case 2:
{
lean_object* v_decl_3169_; lean_object* v___x_3170_; 
v_decl_3169_ = lean_ctor_get(v_decl_3129_, 0);
lean_inc_ref(v_decl_3169_);
v___x_3170_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3163_, v___x_3164_, v_decl_3169_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
v___y_3138_ = v___x_3170_;
goto v___jp_3137_;
}
case 3:
{
lean_object* v_fvarId_3171_; lean_object* v_y_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_fvarId_3171_ = lean_ctor_get(v_decl_3129_, 0);
v_y_3172_ = lean_ctor_get(v_decl_3129_, 2);
lean_inc(v_fvarId_3171_);
v___x_3173_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3171_, v_a_3130_);
lean_dec_ref(v___x_3173_);
lean_inc(v_y_3172_);
v___x_3174_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3164_, v_y_3172_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
v___y_3138_ = v___x_3174_;
goto v___jp_3137_;
}
case 4:
{
lean_object* v_fvarId_3175_; lean_object* v_y_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_fvarId_3175_ = lean_ctor_get(v_decl_3129_, 0);
v_y_3176_ = lean_ctor_get(v_decl_3129_, 2);
lean_inc(v_fvarId_3175_);
v___x_3177_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3175_, v_a_3130_);
lean_dec_ref(v___x_3177_);
lean_inc(v_y_3176_);
v___x_3178_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3176_, v_a_3130_);
v___y_3138_ = v___x_3178_;
goto v___jp_3137_;
}
case 5:
{
lean_object* v_fvarId_3179_; lean_object* v_y_3180_; lean_object* v_ty_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_fvarId_3179_ = lean_ctor_get(v_decl_3129_, 0);
v_y_3180_ = lean_ctor_get(v_decl_3129_, 3);
v_ty_3181_ = lean_ctor_get(v_decl_3129_, 4);
lean_inc(v_fvarId_3179_);
v___x_3182_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3179_, v_a_3130_);
lean_dec_ref(v___x_3182_);
lean_inc(v_y_3180_);
v___x_3183_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3180_, v_a_3130_);
lean_dec_ref(v___x_3183_);
lean_inc_ref(v_ty_3181_);
v___x_3184_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3164_, v_ty_3181_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
v___y_3138_ = v___x_3184_;
goto v___jp_3137_;
}
default: 
{
lean_object* v_fvarId_3185_; lean_object* v___x_3186_; 
v_fvarId_3185_ = lean_ctor_get(v_decl_3129_, 0);
lean_inc(v_fvarId_3185_);
v___x_3186_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3185_, v_a_3130_);
v___y_3138_ = v___x_3186_;
goto v___jp_3137_;
}
}
v___jp_3137_:
{
if (lean_obj_tag(v___y_3138_) == 0)
{
lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3161_; 
v_isSharedCheck_3161_ = !lean_is_exclusive(v___y_3138_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___y_3138_, 0);
lean_dec(v_unused_3162_);
v___x_3140_ = v___y_3138_;
v_isShared_3141_ = v_isSharedCheck_3161_;
goto v_resetjp_3139_;
}
else
{
lean_dec(v___y_3138_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3161_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v_decision_3143_; lean_object* v_newArms_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3160_; 
v___x_3142_ = lean_st_ref_take(v_a_3130_);
v_decision_3143_ = lean_ctor_get(v___x_3142_, 0);
v_newArms_3144_ = lean_ctor_get(v___x_3142_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3146_ = v___x_3142_;
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_newArms_3144_);
lean_inc(v_decision_3143_);
lean_dec(v___x_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3148_ = lean_box(2);
v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3144_, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_decl_3129_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3144_, v___x_3148_, v___x_3150_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 1, v___x_3151_);
v___x_3153_ = v___x_3146_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_decision_3143_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = lean_st_ref_set(v_a_3130_, v___x_3153_);
v___x_3155_ = lean_box(0);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3155_);
v___x_3157_ = v___x_3140_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3129_);
return v___y_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec(v_a_3188_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3196_, lean_object* v_f_3197_, lean_object* v_arg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3197_, v_arg_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3207_, lean_object* v_f_3208_, lean_object* v_arg_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
uint8_t v_pu_boxed_3217_; lean_object* v_res_3218_; 
v_pu_boxed_3217_ = lean_unbox(v_pu_3207_);
v_res_3218_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3217_, v_f_3208_, v_arg_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec(v___y_3210_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3219_, lean_object* v_f_3220_, lean_object* v_param_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3220_, v_param_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3230_, lean_object* v_f_3231_, lean_object* v_param_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
uint8_t v_pu_boxed_3240_; lean_object* v_res_3241_; 
v_pu_boxed_3240_ = lean_unbox(v_pu_3230_);
v_res_3241_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3240_, v_f_3231_, v_param_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3233_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3242_, lean_object* v_alt_3243_, lean_object* v_f_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3243_, v_f_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3253_, lean_object* v_alt_3254_, lean_object* v_f_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v_pu_boxed_3263_; lean_object* v_res_3264_; 
v_pu_boxed_3263_ = lean_unbox(v_pu_3253_);
v_res_3264_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3263_, v_alt_3254_, v_f_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec(v___y_3256_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3265_, lean_object* v_arm_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; lean_object* v_decision_3286_; lean_object* v___x_3287_; 
v___x_3269_ = lean_st_ref_get(v_a_3267_);
v_decision_3286_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_decision_3286_);
lean_dec(v___x_3269_);
v___x_3287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3286_, v_fvar_3265_);
lean_dec_ref(v_decision_3286_);
if (lean_obj_tag(v___x_3287_) == 1)
{
lean_object* v_val_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3315_; 
v_val_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3315_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_val_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3315_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3292_ = lean_box(3);
v___x_3293_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3288_, v___x_3292_);
if (v___x_3293_ == 0)
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3288_, v_arm_3266_);
lean_dec(v_arm_3266_);
lean_dec(v_val_3288_);
if (v___x_3294_ == 0)
{
lean_del_object(v___x_3290_);
goto v___jp_3270_;
}
else
{
if (v___x_3293_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_dec(v_fvar_3265_);
v___x_3295_ = lean_box(0);
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3295_);
v___x_3297_ = v___x_3290_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
else
{
lean_del_object(v___x_3290_);
goto v___jp_3270_;
}
}
}
else
{
lean_object* v___x_3299_; lean_object* v_decision_3300_; lean_object* v_newArms_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_val_3288_);
v___x_3299_ = lean_st_ref_take(v_a_3267_);
v_decision_3300_ = lean_ctor_get(v___x_3299_, 0);
v_newArms_3301_ = lean_ctor_get(v___x_3299_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3303_ = v___x_3299_;
v_isShared_3304_ = v_isSharedCheck_3314_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_newArms_3301_);
lean_inc(v_decision_3300_);
lean_dec(v___x_3299_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3314_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3300_, v_fvar_3265_, v_arm_3266_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3305_);
v___x_3307_ = v___x_3303_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_newArms_3301_);
v___x_3307_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3308_ = lean_st_ref_set(v_a_3267_, v___x_3307_);
v___x_3309_ = lean_box(0);
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3309_);
v___x_3311_ = v___x_3290_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_dec(v___x_3287_);
lean_dec(v_arm_3266_);
lean_dec(v_fvar_3265_);
v___x_3316_ = lean_box(0);
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
return v___x_3317_;
}
v___jp_3270_:
{
lean_object* v___x_3271_; lean_object* v_decision_3272_; lean_object* v_newArms_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3285_; 
v___x_3271_ = lean_st_ref_take(v_a_3267_);
v_decision_3272_ = lean_ctor_get(v___x_3271_, 0);
v_newArms_3273_ = lean_ctor_get(v___x_3271_, 1);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3275_ = v___x_3271_;
v_isShared_3276_ = v_isSharedCheck_3285_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_newArms_3273_);
lean_inc(v_decision_3272_);
lean_dec(v___x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3285_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3277_ = lean_box(2);
v___x_3278_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3272_, v_fvar_3265_, v___x_3277_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3278_);
v___x_3280_ = v___x_3275_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_newArms_3273_);
v___x_3280_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_st_ref_set(v_a_3267_, v___x_3280_);
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3318_, lean_object* v_arm_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3318_, v_arm_3319_, v_a_3320_);
lean_dec(v_a_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3323_, lean_object* v_arm_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3323_, v_arm_3324_, v_a_3325_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3333_, lean_object* v_arm_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3333_, v_arm_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec(v_a_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3344_, v___x_3343_, v___y_3345_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3353_, lean_object* v_x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3353_, v_x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3363_){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3365_ = lean_panic_fn_borrowed(v___x_3364_, v_msg_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3366_, lean_object* v_x_3367_){
_start:
{
if (lean_obj_tag(v_x_3367_) == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3369_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3368_);
return v___x_3369_;
}
else
{
lean_object* v_key_3370_; lean_object* v_value_3371_; lean_object* v_tail_3372_; uint8_t v___x_3373_; 
v_key_3370_ = lean_ctor_get(v_x_3367_, 0);
v_value_3371_ = lean_ctor_get(v_x_3367_, 1);
v_tail_3372_ = lean_ctor_get(v_x_3367_, 2);
v___x_3373_ = l_Lean_instBEqFVarId_beq(v_key_3370_, v_a_3366_);
if (v___x_3373_ == 0)
{
v_x_3367_ = v_tail_3372_;
goto _start;
}
else
{
lean_inc(v_value_3371_);
return v_value_3371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3375_, v_x_3376_);
lean_dec(v_x_3376_);
lean_dec(v_a_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_buckets_3380_; lean_object* v___x_3381_; uint64_t v___x_3382_; uint64_t v___x_3383_; uint64_t v___x_3384_; uint64_t v_fold_3385_; uint64_t v___x_3386_; uint64_t v___x_3387_; uint64_t v___x_3388_; size_t v___x_3389_; size_t v___x_3390_; size_t v___x_3391_; size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_buckets_3380_ = lean_ctor_get(v_m_3378_, 1);
v___x_3381_ = lean_array_get_size(v_buckets_3380_);
v___x_3382_ = l_Lean_instHashableFVarId_hash(v_a_3379_);
v___x_3383_ = 32ULL;
v___x_3384_ = lean_uint64_shift_right(v___x_3382_, v___x_3383_);
v_fold_3385_ = lean_uint64_xor(v___x_3382_, v___x_3384_);
v___x_3386_ = 16ULL;
v___x_3387_ = lean_uint64_shift_right(v_fold_3385_, v___x_3386_);
v___x_3388_ = lean_uint64_xor(v_fold_3385_, v___x_3387_);
v___x_3389_ = lean_uint64_to_usize(v___x_3388_);
v___x_3390_ = lean_usize_of_nat(v___x_3381_);
v___x_3391_ = ((size_t)1ULL);
v___x_3392_ = lean_usize_sub(v___x_3390_, v___x_3391_);
v___x_3393_ = lean_usize_land(v___x_3389_, v___x_3392_);
v___x_3394_ = lean_array_uget_borrowed(v_buckets_3380_, v___x_3393_);
v___x_3395_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3379_, v___x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3396_, v_a_3397_);
lean_dec(v_a_3397_);
lean_dec_ref(v_m_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v___x_3407_; lean_object* v_decision_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3465_; 
v___x_3407_ = lean_st_ref_get(v_a_3400_);
v_decision_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v___x_3407_, 1);
lean_dec(v_unused_3466_);
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3465_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_decision_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3465_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
uint8_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___y_3416_; lean_object* v___f_3442_; 
v___x_3412_ = 0;
v___x_3413_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3399_);
v___x_3414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3408_, v___x_3413_);
lean_dec(v___x_3413_);
lean_dec_ref(v_decision_3408_);
lean_inc(v___x_3414_);
v___f_3442_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3442_, 0, v___x_3414_);
switch(lean_obj_tag(v_decl_3399_))
{
case 0:
{
lean_object* v_decl_3443_; lean_object* v___x_3444_; 
v_decl_3443_ = lean_ctor_get(v_decl_3399_, 0);
lean_inc_ref(v_decl_3443_);
v___x_3444_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3412_, v___f_3442_, v_decl_3443_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
v___y_3416_ = v___x_3444_;
goto v___jp_3415_;
}
case 1:
{
lean_object* v_decl_3445_; lean_object* v___x_3446_; 
v_decl_3445_ = lean_ctor_get(v_decl_3399_, 0);
lean_inc_ref(v_decl_3445_);
v___x_3446_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3412_, v___f_3442_, v_decl_3445_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
v___y_3416_ = v___x_3446_;
goto v___jp_3415_;
}
case 2:
{
lean_object* v_decl_3447_; lean_object* v___x_3448_; 
v_decl_3447_ = lean_ctor_get(v_decl_3399_, 0);
lean_inc_ref(v_decl_3447_);
v___x_3448_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3412_, v___f_3442_, v_decl_3447_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
v___y_3416_ = v___x_3448_;
goto v___jp_3415_;
}
case 3:
{
lean_object* v_fvarId_3449_; lean_object* v_y_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_fvarId_3449_ = lean_ctor_get(v_decl_3399_, 0);
v_y_3450_ = lean_ctor_get(v_decl_3399_, 2);
lean_inc(v___x_3414_);
lean_inc(v_fvarId_3449_);
v___x_3451_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3449_, v___x_3414_, v_a_3400_);
lean_dec_ref(v___x_3451_);
lean_inc(v_y_3450_);
v___x_3452_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3442_, v_y_3450_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
v___y_3416_ = v___x_3452_;
goto v___jp_3415_;
}
case 4:
{
lean_object* v_fvarId_3453_; lean_object* v_y_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec_ref(v___f_3442_);
v_fvarId_3453_ = lean_ctor_get(v_decl_3399_, 0);
v_y_3454_ = lean_ctor_get(v_decl_3399_, 2);
lean_inc_n(v___x_3414_, 2);
lean_inc(v_fvarId_3453_);
v___x_3455_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3453_, v___x_3414_, v_a_3400_);
lean_dec_ref(v___x_3455_);
lean_inc(v_y_3454_);
v___x_3456_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3454_, v___x_3414_, v_a_3400_);
v___y_3416_ = v___x_3456_;
goto v___jp_3415_;
}
case 5:
{
lean_object* v_fvarId_3457_; lean_object* v_y_3458_; lean_object* v_ty_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_fvarId_3457_ = lean_ctor_get(v_decl_3399_, 0);
v_y_3458_ = lean_ctor_get(v_decl_3399_, 3);
v_ty_3459_ = lean_ctor_get(v_decl_3399_, 4);
lean_inc_n(v___x_3414_, 2);
lean_inc(v_fvarId_3457_);
v___x_3460_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3457_, v___x_3414_, v_a_3400_);
lean_dec_ref(v___x_3460_);
lean_inc(v_y_3458_);
v___x_3461_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3458_, v___x_3414_, v_a_3400_);
lean_dec_ref(v___x_3461_);
lean_inc_ref(v_ty_3459_);
v___x_3462_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3442_, v_ty_3459_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
v___y_3416_ = v___x_3462_;
goto v___jp_3415_;
}
default: 
{
lean_object* v_fvarId_3463_; lean_object* v___x_3464_; 
lean_dec_ref(v___f_3442_);
v_fvarId_3463_ = lean_ctor_get(v_decl_3399_, 0);
lean_inc(v___x_3414_);
lean_inc(v_fvarId_3463_);
v___x_3464_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3463_, v___x_3414_, v_a_3400_);
v___y_3416_ = v___x_3464_;
goto v___jp_3415_;
}
}
v___jp_3415_:
{
if (lean_obj_tag(v___y_3416_) == 0)
{
lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3440_; 
v_isSharedCheck_3440_ = !lean_is_exclusive(v___y_3416_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; 
v_unused_3441_ = lean_ctor_get(v___y_3416_, 0);
lean_dec(v_unused_3441_);
v___x_3418_ = v___y_3416_;
v_isShared_3419_ = v_isSharedCheck_3440_;
goto v_resetjp_3417_;
}
else
{
lean_dec(v___y_3416_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3440_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v_decision_3421_; lean_object* v_newArms_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3439_; 
v___x_3420_ = lean_st_ref_take(v_a_3400_);
v_decision_3421_ = lean_ctor_get(v___x_3420_, 0);
v_newArms_3422_ = lean_ctor_get(v___x_3420_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3424_ = v___x_3420_;
v_isShared_3425_ = v_isSharedCheck_3439_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_newArms_3422_);
lean_inc(v_decision_3421_);
lean_dec(v___x_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3439_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3422_, v___x_3414_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 1);
lean_ctor_set(v___x_3410_, 1, v___x_3426_);
lean_ctor_set(v___x_3410_, 0, v_decl_3399_);
v___x_3428_ = v___x_3410_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_decl_3399_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3422_, v___x_3414_, v___x_3428_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3429_);
v___x_3431_ = v___x_3424_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_decision_3421_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3432_ = lean_st_ref_set(v_a_3400_, v___x_3431_);
v___x_3433_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3433_);
v___x_3435_ = v___x_3418_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3414_);
lean_del_object(v___x_3410_);
lean_dec_ref(v_decl_3399_);
return v___y_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec(v_a_3468_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3476_, lean_object* v_b_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
if (lean_obj_tag(v_as_x27_3476_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_b_3477_);
return v___x_3485_;
}
else
{
lean_object* v_head_3486_; lean_object* v_tail_3487_; lean_object* v___x_3488_; lean_object* v_decision_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_head_3486_ = lean_ctor_get(v_as_x27_3476_, 0);
lean_inc(v_head_3486_);
v_tail_3487_ = lean_ctor_get(v_as_x27_3476_, 1);
lean_inc(v_tail_3487_);
lean_dec_ref(v_as_x27_3476_);
v___x_3488_ = lean_st_ref_get(v___y_3478_);
v_decision_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc_ref(v_decision_3489_);
lean_dec(v___x_3488_);
v___x_3490_ = lean_box(0);
v___x_3491_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3486_);
v___x_3492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3489_, v___x_3491_);
lean_dec(v___x_3491_);
lean_dec_ref(v_decision_3489_);
v___x_3493_ = lean_box(3);
v___x_3494_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3495_ = lean_box(2);
v___x_3496_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3492_, v___x_3495_);
lean_dec(v___x_3492_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3486_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_dec_ref(v___x_3497_);
v_as_x27_3476_ = v_tail_3487_;
v_b_3477_ = v___x_3490_;
goto _start;
}
else
{
lean_dec(v_tail_3487_);
return v___x_3497_;
}
}
else
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3486_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_dec_ref(v___x_3499_);
v_as_x27_3476_ = v_tail_3487_;
v_b_3477_ = v___x_3490_;
goto _start;
}
else
{
lean_dec(v_tail_3487_);
return v___x_3499_;
}
}
}
else
{
uint8_t v___x_3501_; lean_object* v___x_3502_; 
lean_dec(v___x_3492_);
v___x_3501_ = 0;
v___x_3502_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3501_, v_head_3486_, v___y_3481_);
lean_dec(v_head_3486_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_dec_ref(v___x_3502_);
v_as_x27_3476_ = v_tail_3487_;
v_b_3477_ = v___x_3490_;
goto _start;
}
else
{
lean_dec(v_tail_3487_);
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3504_, lean_object* v_b_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3504_, v_b_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec(v___y_3506_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_box(0);
lean_inc(v_a_3515_);
v___x_3522_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3515_, v___x_3521_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v___x_3522_, 0);
lean_dec(v_unused_3530_);
v___x_3524_ = v___x_3522_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v___x_3522_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3521_);
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3521_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
else
{
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec(v_a_3531_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3539_, lean_object* v_as_x27_3540_, lean_object* v_b_3541_, lean_object* v_a_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3540_, v_b_3541_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_3551_, lean_object* v_as_x27_3552_, lean_object* v_b_3553_, lean_object* v_a_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3551_, v_as_x27_3552_, v_b_3553_, v_a_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec(v_as_3551_);
return v_res_3562_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
lean_ctor_set(v___x_3568_, 2, v___x_3567_);
lean_ctor_set(v___x_3568_, 3, v___x_3567_);
lean_ctor_set(v___x_3568_, 4, v___x_3566_);
lean_ctor_set(v___x_3568_, 5, v___x_3566_);
lean_ctor_set(v___x_3568_, 6, v___x_3566_);
lean_ctor_set(v___x_3568_, 7, v___x_3566_);
lean_ctor_set(v___x_3568_, 8, v___x_3566_);
lean_ctor_set(v___x_3568_, 9, v___x_3566_);
return v___x_3568_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3569_; double v___x_3570_; 
v___x_3569_ = lean_unsigned_to_nat(0u);
v___x_3570_ = lean_float_of_nat(v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3574_, lean_object* v_msg_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_options_3581_; lean_object* v_ref_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_options_3581_ = lean_ctor_get(v___y_3578_, 2);
v_ref_3582_ = lean_ctor_get(v___y_3578_, 5);
v___x_3583_ = lean_st_ref_get(v___y_3579_);
v___x_3584_ = lean_st_ref_get(v___y_3577_);
v___x_3585_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3576_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3644_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3644_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3644_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v_env_3590_; lean_object* v_lctx_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3642_; 
v_env_3590_ = lean_ctor_get(v___x_3583_, 0);
lean_inc_ref(v_env_3590_);
lean_dec(v___x_3583_);
v_lctx_3591_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v___x_3584_, 1);
lean_dec(v_unused_3643_);
v___x_3593_ = v___x_3584_;
v_isShared_3594_ = v_isSharedCheck_3642_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_lctx_3591_);
lean_dec(v___x_3584_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3642_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_traceState_3597_; lean_object* v_env_3598_; lean_object* v_nextMacroScope_3599_; lean_object* v_ngen_3600_; lean_object* v_auxDeclNGen_3601_; lean_object* v_cache_3602_; lean_object* v_messages_3603_; lean_object* v_infoState_3604_; lean_object* v_snapshotTasks_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3641_; 
v___x_3595_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3596_ = lean_st_ref_take(v___y_3579_);
v_traceState_3597_ = lean_ctor_get(v___x_3596_, 4);
v_env_3598_ = lean_ctor_get(v___x_3596_, 0);
v_nextMacroScope_3599_ = lean_ctor_get(v___x_3596_, 1);
v_ngen_3600_ = lean_ctor_get(v___x_3596_, 2);
v_auxDeclNGen_3601_ = lean_ctor_get(v___x_3596_, 3);
v_cache_3602_ = lean_ctor_get(v___x_3596_, 5);
v_messages_3603_ = lean_ctor_get(v___x_3596_, 6);
v_infoState_3604_ = lean_ctor_get(v___x_3596_, 7);
v_snapshotTasks_3605_ = lean_ctor_get(v___x_3596_, 8);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3607_ = v___x_3596_;
v_isShared_3608_ = v_isSharedCheck_3641_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_snapshotTasks_3605_);
lean_inc(v_infoState_3604_);
lean_inc(v_messages_3603_);
lean_inc(v_cache_3602_);
lean_inc(v_traceState_3597_);
lean_inc(v_auxDeclNGen_3601_);
lean_inc(v_ngen_3600_);
lean_inc(v_nextMacroScope_3599_);
lean_inc(v_env_3598_);
lean_dec(v___x_3596_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3641_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
uint64_t v_tid_3609_; lean_object* v_traces_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3640_; 
v_tid_3609_ = lean_ctor_get_uint64(v_traceState_3597_, sizeof(void*)*1);
v_traces_3610_ = lean_ctor_get(v_traceState_3597_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_traceState_3597_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3612_ = v_traceState_3597_;
v_isShared_3613_ = v_isSharedCheck_3640_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_traces_3610_);
lean_dec(v_traceState_3597_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3640_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3614_ = lean_unbox(v_a_3586_);
lean_dec(v_a_3586_);
v___x_3615_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3591_, v___x_3614_);
lean_dec_ref(v_lctx_3591_);
lean_inc_ref(v_options_3581_);
v___x_3616_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3616_, 0, v_env_3590_);
lean_ctor_set(v___x_3616_, 1, v___x_3595_);
lean_ctor_set(v___x_3616_, 2, v___x_3615_);
lean_ctor_set(v___x_3616_, 3, v_options_3581_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 3);
lean_ctor_set(v___x_3593_, 1, v_msg_3575_);
lean_ctor_set(v___x_3593_, 0, v___x_3616_);
v___x_3618_ = v___x_3593_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_msg_3575_);
v___x_3618_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; double v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3619_ = lean_box(0);
v___x_3620_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3621_ = 0;
v___x_3622_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3623_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3623_, 0, v_cls_3574_);
lean_ctor_set(v___x_3623_, 1, v___x_3619_);
lean_ctor_set(v___x_3623_, 2, v___x_3622_);
lean_ctor_set_float(v___x_3623_, sizeof(void*)*3, v___x_3620_);
lean_ctor_set_float(v___x_3623_, sizeof(void*)*3 + 8, v___x_3620_);
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*3 + 16, v___x_3621_);
v___x_3624_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3625_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3618_);
lean_ctor_set(v___x_3625_, 2, v___x_3624_);
lean_inc(v_ref_3582_);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_ref_3582_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l_Lean_PersistentArray_push___redArg(v_traces_3610_, v___x_3626_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3627_);
v___x_3629_ = v___x_3612_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3627_);
lean_ctor_set_uint64(v_reuseFailAlloc_3638_, sizeof(void*)*1, v_tid_3609_);
v___x_3629_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3631_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 4, v___x_3629_);
v___x_3631_ = v___x_3607_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_env_3598_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_nextMacroScope_3599_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_ngen_3600_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_auxDeclNGen_3601_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3637_, 5, v_cache_3602_);
lean_ctor_set(v_reuseFailAlloc_3637_, 6, v_messages_3603_);
lean_ctor_set(v_reuseFailAlloc_3637_, 7, v_infoState_3604_);
lean_ctor_set(v_reuseFailAlloc_3637_, 8, v_snapshotTasks_3605_);
v___x_3631_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3632_ = lean_st_ref_set(v___y_3579_, v___x_3631_);
v___x_3633_ = lean_box(0);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v___x_3633_);
v___x_3635_ = v___x_3588_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
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
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v___x_3584_);
lean_dec(v___x_3583_);
lean_dec_ref(v_msg_3575_);
lean_dec(v_cls_3574_);
v_a_3645_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3585_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3585_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3653_, lean_object* v_msg_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3653_, v_msg_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3661_, lean_object* v_msg_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3661_, v_msg_3662_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3670_, lean_object* v_msg_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3670_, v_msg_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
return v_res_3678_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3687_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3688_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3689_ = l_Lean_Name_append(v___x_3688_, v___x_3687_);
return v___x_3689_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
return v___x_3692_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3695_ = l_Lean_stringToMessageData(v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
switch(lean_obj_tag(v_code_3696_))
{
case 0:
{
lean_object* v_decl_3703_; lean_object* v_k_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_decl_3703_ = lean_ctor_get(v_code_3696_, 0);
lean_inc_ref(v_decl_3703_);
v_k_3704_ = lean_ctor_get(v_code_3696_, 1);
lean_inc_ref(v_k_3704_);
lean_dec_ref(v_code_3696_);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_decl_3703_);
v___x_3706_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3706_, 0, v_k_3704_);
v___x_3707_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3705_, v___x_3706_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
return v___x_3707_;
}
case 1:
{
lean_object* v_decl_3708_; lean_object* v_k_3709_; lean_object* v_params_3710_; lean_object* v_type_3711_; lean_object* v_value_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_decl_3708_ = lean_ctor_get(v_code_3696_, 0);
lean_inc_ref(v_decl_3708_);
v_k_3709_ = lean_ctor_get(v_code_3696_, 1);
lean_inc_ref(v_k_3709_);
lean_dec_ref(v_code_3696_);
v_params_3710_ = lean_ctor_get(v_decl_3708_, 2);
lean_inc_ref(v_params_3710_);
v_type_3711_ = lean_ctor_get(v_decl_3708_, 3);
lean_inc_ref(v_type_3711_);
v_value_3712_ = lean_ctor_get(v_decl_3708_, 4);
lean_inc_ref(v_value_3712_);
v___x_3713_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3713_, 0, v_value_3712_);
v___x_3714_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3713_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3735_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3735_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3735_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
uint8_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = 0;
v___x_3720_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3719_, v_decl_3708_, v_type_3711_, v_params_3710_, v_a_3715_, v_a_3699_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref(v___x_3720_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set_tag(v___x_3717_, 1);
lean_ctor_set(v___x_3717_, 0, v_a_3721_);
v___x_3723_ = v___x_3717_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3721_);
v___x_3723_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3724_, 0, v_k_3709_);
v___x_3725_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3723_, v___x_3724_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
return v___x_3725_;
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3717_);
lean_dec_ref(v_k_3709_);
v_a_3727_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3720_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3720_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3711_);
lean_dec_ref(v_params_3710_);
lean_dec_ref(v_k_3709_);
lean_dec_ref(v_decl_3708_);
return v___x_3714_;
}
}
case 2:
{
lean_object* v_decl_3736_; lean_object* v_k_3737_; lean_object* v_params_3738_; lean_object* v_type_3739_; lean_object* v_value_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_decl_3736_ = lean_ctor_get(v_code_3696_, 0);
lean_inc_ref(v_decl_3736_);
v_k_3737_ = lean_ctor_get(v_code_3696_, 1);
lean_inc_ref(v_k_3737_);
lean_dec_ref(v_code_3696_);
v_params_3738_ = lean_ctor_get(v_decl_3736_, 2);
lean_inc_ref(v_params_3738_);
v_type_3739_ = lean_ctor_get(v_decl_3736_, 3);
lean_inc_ref(v_type_3739_);
v_value_3740_ = lean_ctor_get(v_decl_3736_, 4);
lean_inc_ref(v_value_3740_);
v___x_3741_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3741_, 0, v_value_3740_);
v___x_3742_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3741_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3763_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3763_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3763_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
uint8_t v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = 0;
v___x_3748_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3747_, v_decl_3736_, v_type_3739_, v_params_3738_, v_a_3743_, v_a_3699_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3751_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref(v___x_3748_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set_tag(v___x_3745_, 2);
lean_ctor_set(v___x_3745_, 0, v_a_3749_);
v___x_3751_ = v___x_3745_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3749_);
v___x_3751_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3752_, 0, v_k_3737_);
v___x_3753_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3751_, v___x_3752_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
return v___x_3753_;
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3745_);
lean_dec_ref(v_k_3737_);
v_a_3755_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3748_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3748_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3739_);
lean_dec_ref(v_params_3738_);
lean_dec_ref(v_k_3737_);
lean_dec_ref(v_decl_3736_);
return v___x_3742_;
}
}
case 4:
{
lean_object* v_cases_3764_; lean_object* v___x_3765_; 
v_cases_3764_ = lean_ctor_get(v_code_3696_, 0);
lean_inc_ref_n(v_cases_3764_, 2);
v___x_3765_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3764_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3764_);
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v_a_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_st_mk_ref(v___x_3768_);
v___x_3770_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3769_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v___x_3771_; lean_object* v_typeName_3772_; lean_object* v_resultType_3773_; lean_object* v_discr_3774_; lean_object* v_alts_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v___x_3770_);
v___x_3771_ = lean_st_ref_get(v___x_3769_);
lean_dec(v___x_3769_);
v_typeName_3772_ = lean_ctor_get(v_cases_3764_, 0);
v_resultType_3773_ = lean_ctor_get(v_cases_3764_, 1);
v_discr_3774_ = lean_ctor_get(v_cases_3764_, 2);
v_alts_3775_ = lean_ctor_get(v_cases_3764_, 3);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_cases_3764_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3777_ = v_cases_3764_;
v_isShared_3778_ = v_isSharedCheck_3818_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_alts_3775_);
lean_inc(v_discr_3774_);
lean_inc(v_resultType_3773_);
lean_inc(v_typeName_3772_);
lean_dec(v_cases_3764_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3818_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v_newArms_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_newArms_3779_ = lean_ctor_get(v___x_3771_, 1);
lean_inc_ref(v_newArms_3779_);
lean_dec(v___x_3771_);
v___x_3780_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3775_);
v___x_3781_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3779_, v___x_3780_, v_alts_3775_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3809_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3809_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3809_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
uint8_t v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___y_3790_; uint8_t v___y_3802_; size_t v___x_3804_; size_t v___x_3805_; uint8_t v___x_3806_; 
v___x_3786_ = 0;
v___x_3787_ = lean_box(2);
v___x_3788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3779_, v___x_3787_);
lean_dec_ref(v_newArms_3779_);
v___x_3804_ = lean_ptr_addr(v_alts_3775_);
lean_dec_ref(v_alts_3775_);
v___x_3805_ = lean_ptr_addr(v_a_3782_);
v___x_3806_ = lean_usize_dec_eq(v___x_3804_, v___x_3805_);
if (v___x_3806_ == 0)
{
v___y_3802_ = v___x_3806_;
goto v___jp_3801_;
}
else
{
size_t v___x_3807_; uint8_t v___x_3808_; 
v___x_3807_ = lean_ptr_addr(v_resultType_3773_);
v___x_3808_ = lean_usize_dec_eq(v___x_3807_, v___x_3807_);
v___y_3802_ = v___x_3808_;
goto v___jp_3801_;
}
v___jp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3791_ = lean_array_mk(v___x_3788_);
v___x_3792_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3786_, v___x_3791_, v___y_3790_);
lean_dec_ref(v___x_3791_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3792_);
v___x_3794_ = v___x_3784_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
v___jp_3796_:
{
lean_object* v___x_3798_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 3, v_a_3782_);
v___x_3798_ = v___x_3777_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_typeName_3772_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_resultType_3773_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_discr_3774_);
lean_ctor_set(v_reuseFailAlloc_3800_, 3, v_a_3782_);
v___x_3798_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
v___y_3790_ = v___x_3799_;
goto v___jp_3789_;
}
}
v___jp_3801_:
{
if (v___y_3802_ == 0)
{
lean_dec_ref(v_code_3696_);
goto v___jp_3796_;
}
else
{
uint8_t v___x_3803_; 
v___x_3803_ = l_Lean_instBEqFVarId_beq(v_discr_3774_, v_discr_3774_);
if (v___x_3803_ == 0)
{
lean_dec_ref(v_code_3696_);
goto v___jp_3796_;
}
else
{
lean_dec(v_a_3782_);
lean_del_object(v___x_3777_);
lean_dec(v_discr_3774_);
lean_dec_ref(v_resultType_3773_);
lean_dec(v_typeName_3772_);
v___y_3790_ = v_code_3696_;
goto v___jp_3789_;
}
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v_newArms_3779_);
lean_del_object(v___x_3777_);
lean_dec_ref(v_alts_3775_);
lean_dec(v_discr_3774_);
lean_dec_ref(v_resultType_3773_);
lean_dec(v_typeName_3772_);
lean_dec_ref(v_code_3696_);
v_a_3810_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3781_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3781_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v___x_3769_);
lean_dec_ref(v_cases_3764_);
lean_dec_ref(v_code_3696_);
v_a_3819_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3770_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3770_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v_cases_3764_);
lean_dec_ref(v_code_3696_);
v_a_3827_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3765_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3765_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
default: 
{
uint8_t v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3835_ = 0;
lean_inc(v_a_3697_);
v___x_3836_ = lean_array_mk(v_a_3697_);
v___x_3837_ = l_Array_reverse___redArg(v___x_3836_);
v___x_3838_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3835_, v___x_3837_, v_code_3696_);
lean_dec_ref(v___x_3837_);
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
return v___x_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3848_, lean_object* v_i_3849_, lean_object* v_as_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3857_ = lean_array_get_size(v_as_3850_);
v___x_3858_ = lean_nat_dec_lt(v_i_3849_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; 
lean_dec(v_i_3849_);
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_as_3850_);
return v___x_3859_;
}
else
{
lean_object* v_options_3860_; lean_object* v_inheritedTraceOptions_3861_; uint8_t v_hasTrace_3862_; uint8_t v___x_3863_; lean_object* v_a_3864_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; 
v_options_3860_ = lean_ctor_get(v___y_3854_, 2);
v_inheritedTraceOptions_3861_ = lean_ctor_get(v___y_3854_, 13);
v_hasTrace_3862_ = lean_ctor_get_uint8(v_options_3860_, sizeof(void*)*1);
v___x_3863_ = 0;
v_a_3864_ = lean_array_fget_borrowed(v_as_3850_, v_i_3849_);
v___x_3895_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3864_);
v___x_3896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3848_, v___x_3895_);
if (v_hasTrace_3862_ == 0)
{
lean_dec(v___x_3895_);
v___y_3898_ = v___y_3852_;
v___y_3899_ = v___y_3853_;
v___y_3900_ = v___y_3854_;
v___y_3901_ = v___y_3855_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3906_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3907_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3861_, v_options_3860_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_dec(v___x_3895_);
v___y_3898_ = v___y_3852_;
v___y_3899_ = v___y_3853_;
v___y_3900_ = v___y_3854_;
v___y_3901_ = v___y_3855_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3909_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3895_, v___x_3910_);
v___x_3912_ = l_Lean_MessageData_ofFormat(v___x_3911_);
v___x_3913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3909_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l_List_lengthTR___redArg(v___x_3896_);
v___x_3917_ = l_Nat_reprFast(v___x_3916_);
v___x_3918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v___x_3919_ = l_Lean_MessageData_ofFormat(v___x_3918_);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3915_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3906_, v___x_3920_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_dec_ref(v___x_3921_);
v___y_3898_ = v___y_3852_;
v___y_3899_ = v___y_3853_;
v___y_3900_ = v___y_3854_;
v___y_3901_ = v___y_3855_;
goto v___jp_3897_;
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v___x_3896_);
lean_dec_ref(v_as_3850_);
lean_dec(v_i_3849_);
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
v___jp_3865_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3863_, v___y_3869_, v___y_3871_);
lean_dec_ref(v___y_3869_);
v___x_3873_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3873_, 0, v___x_3872_);
v___x_3874_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3873_, v___y_3870_, v___y_3867_, v___y_3866_, v___y_3868_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; uint8_t v___x_3879_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
lean_inc(v_a_3864_);
v___x_3876_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3864_, v_a_3875_);
v___x_3877_ = lean_ptr_addr(v_a_3864_);
v___x_3878_ = lean_ptr_addr(v___x_3876_);
v___x_3879_ = lean_usize_dec_eq(v___x_3877_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_unsigned_to_nat(1u);
v___x_3881_ = lean_nat_add(v_i_3849_, v___x_3880_);
v___x_3882_ = lean_array_fset(v_as_3850_, v_i_3849_, v___x_3876_);
lean_dec(v_i_3849_);
v_i_3849_ = v___x_3881_;
v_as_3850_ = v___x_3882_;
goto _start;
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_dec_ref(v___x_3876_);
v___x_3884_ = lean_unsigned_to_nat(1u);
v___x_3885_ = lean_nat_add(v_i_3849_, v___x_3884_);
lean_dec(v_i_3849_);
v_i_3849_ = v___x_3885_;
goto _start;
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_as_3850_);
lean_dec(v_i_3849_);
v_a_3887_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3874_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3874_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
v___jp_3897_:
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_array_mk(v___x_3896_);
switch(lean_obj_tag(v_a_3864_))
{
case 0:
{
lean_object* v_code_3903_; 
v_code_3903_ = lean_ctor_get(v_a_3864_, 2);
lean_inc_ref(v_code_3903_);
v___y_3866_ = v___y_3900_;
v___y_3867_ = v___y_3899_;
v___y_3868_ = v___y_3901_;
v___y_3869_ = v___x_3902_;
v___y_3870_ = v___y_3898_;
v___y_3871_ = v_code_3903_;
goto v___jp_3865_;
}
case 1:
{
lean_object* v_code_3904_; 
v_code_3904_ = lean_ctor_get(v_a_3864_, 1);
lean_inc_ref(v_code_3904_);
v___y_3866_ = v___y_3900_;
v___y_3867_ = v___y_3899_;
v___y_3868_ = v___y_3901_;
v___y_3869_ = v___x_3902_;
v___y_3870_ = v___y_3898_;
v___y_3871_ = v_code_3904_;
goto v___jp_3865_;
}
default: 
{
lean_object* v_code_3905_; 
v_code_3905_ = lean_ctor_get(v_a_3864_, 0);
lean_inc_ref(v_code_3905_);
v___y_3866_ = v___y_3900_;
v___y_3867_ = v___y_3899_;
v___y_3868_ = v___y_3901_;
v___y_3869_ = v___x_3902_;
v___y_3870_ = v___y_3898_;
v___y_3871_ = v_code_3905_;
goto v___jp_3865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3930_, lean_object* v_i_3931_, lean_object* v_as_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3930_, v_i_3931_, v_as_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___x_3930_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3940_, lean_object* v_v_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
if (lean_obj_tag(v_v_3941_) == 0)
{
lean_object* v_code_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3972_; 
v_code_3948_ = lean_ctor_get(v_v_3941_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_v_3941_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3950_ = v_v_3941_;
v_isShared_3951_ = v_isSharedCheck_3972_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_code_3948_);
lean_dec(v_v_3941_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3972_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3952_; 
lean_inc(v___y_3946_);
lean_inc_ref(v___y_3945_);
lean_inc(v___y_3944_);
lean_inc_ref(v___y_3943_);
lean_inc(v___y_3942_);
v___x_3952_ = lean_apply_7(v_f_3940_, v_code_3948_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, lean_box(0));
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3963_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v_a_3953_);
v___x_3958_ = v___x_3950_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3960_; 
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_3958_);
v___x_3960_ = v___x_3955_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_del_object(v___x_3950_);
v_a_3964_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3952_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3952_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_object* v___x_3973_; 
lean_dec_ref(v_f_3940_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_v_3941_);
return v___x_3973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3974_, lean_object* v_v_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3974_, v_v_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3983_, lean_object* v_f_3984_, lean_object* v_v_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3984_, v_v_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3993_, lean_object* v_f_3994_, lean_object* v_v_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
uint8_t v_pu_boxed_4002_; lean_object* v_res_4003_; 
v_pu_boxed_4002_ = lean_unbox(v_pu_3993_);
v_res_4003_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_4002_, v_f_3994_, v_v_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_toSignature_4011_; lean_object* v_value_4012_; uint8_t v_recursive_4013_; lean_object* v_inlineAttr_x3f_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4040_; 
v_toSignature_4011_ = lean_ctor_get(v_decl_4005_, 0);
v_value_4012_ = lean_ctor_get(v_decl_4005_, 1);
v_recursive_4013_ = lean_ctor_get_uint8(v_decl_4005_, sizeof(void*)*3);
v_inlineAttr_x3f_4014_ = lean_ctor_get(v_decl_4005_, 2);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_decl_4005_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4016_ = v_decl_4005_;
v_isShared_4017_ = v_isSharedCheck_4040_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_inlineAttr_x3f_4014_);
lean_inc(v_value_4012_);
lean_inc(v_toSignature_4011_);
lean_dec(v_decl_4005_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4040_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4018_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_4019_ = lean_box(0);
v___x_4020_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_4018_, v_value_4012_, v___x_4019_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4031_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4031_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4031_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 1, v_a_4021_);
v___x_4026_ = v___x_4016_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_toSignature_4011_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_a_4021_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_inlineAttr_x3f_4014_);
lean_ctor_set_uint8(v_reuseFailAlloc_4030_, sizeof(void*)*3, v_recursive_4013_);
v___x_4026_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4028_; 
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v___x_4026_);
v___x_4028_ = v___x_4023_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_del_object(v___x_4016_);
lean_dec(v_inlineAttr_x3f_4014_);
lean_dec_ref(v_toSignature_4011_);
v_a_4032_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4020_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4020_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_4064_, lean_object* v___f_4065_, lean_object* v_occurrence_4066_, lean_object* v_h_4067_){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_4069_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_4068_, v_phase_4064_, v___f_4065_, v_occurrence_4066_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_4070_, lean_object* v___f_4071_, lean_object* v_occurrence_4072_, lean_object* v_h_4073_){
_start:
{
uint8_t v_phase_boxed_4074_; lean_object* v_res_4075_; 
v_phase_boxed_4074_ = lean_unbox(v_phase_4070_);
v_res_4075_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_4074_, v___f_4071_, v_occurrence_4072_, v_h_4073_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_4077_, lean_object* v_occurrence_4078_){
_start:
{
lean_object* v___f_4079_; lean_object* v___x_4080_; lean_object* v___f_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; 
v___f_4079_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_4080_ = lean_box(v_phase_4077_);
v___f_4081_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4081_, 0, v___x_4080_);
lean_closure_set(v___f_4081_, 1, v___f_4079_);
lean_closure_set(v___f_4081_, 2, v_occurrence_4078_);
v___x_4082_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_4083_ = 0;
v___x_4084_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_4082_, v_phase_4077_, v___x_4083_, v___f_4081_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_4085_, lean_object* v_occurrence_4086_){
_start:
{
uint8_t v_phase_boxed_4087_; lean_object* v_res_4088_; 
v_phase_boxed_4087_ = lean_unbox(v_phase_4085_);
v_res_4088_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_4087_, v_occurrence_4086_);
return v_res_4088_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4140_ = lean_unsigned_to_nat(3411573818u);
v___x_4141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4142_ = l_Lean_Name_num___override(v___x_4141_, v___x_4140_);
return v___x_4142_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4145_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4146_ = l_Lean_Name_str___override(v___x_4145_, v___x_4144_);
return v___x_4146_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4149_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4150_ = l_Lean_Name_str___override(v___x_4149_, v___x_4148_);
return v___x_4150_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4151_ = lean_unsigned_to_nat(2u);
v___x_4152_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4153_ = l_Lean_Name_num___override(v___x_4152_, v___x_4151_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4155_; uint8_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4155_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4156_ = 1;
v___x_4157_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4158_ = l_Lean_registerTraceClass(v___x_4155_, v___x_4156_, v___x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4160_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
