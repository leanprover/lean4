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
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v_x_116_, 1);
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
lean_dec_ref_known(v_value_256_, 3);
v___x_264_ = l_Lean_Compiler_LCNF_getType(v_struct_263_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
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
lean_dec_ref_known(v_a_267_, 1);
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
lean_dec_ref_known(v_a_258_, 1);
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
lean_dec_ref_known(v___x_565_, 1);
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
lean_dec_ref_known(v___y_560_, 1);
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
lean_dec_ref_known(v___x_599_, 1);
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
lean_dec_ref_known(v___x_633_, 1);
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
lean_dec_ref_known(v___y_628_, 1);
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
lean_dec_ref_known(v_value_648_, 3);
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
lean_dec_ref_known(v_value_648_, 3);
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
lean_dec_ref_known(v_a_675_, 1);
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
lean_dec_ref_known(v_value_648_, 2);
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
lean_dec_ref_known(v_value_837_, 1);
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
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1006_; 
v_val_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1006_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1006_;
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
uint8_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_981_, v_plannedDecision_975_);
lean_dec(v_plannedDecision_975_);
lean_dec(v_val_981_);
v___x_993_ = lean_bool_not(v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_dec(v_var_976_);
v___x_994_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 0, v___x_994_);
v___x_996_ = v___x_983_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_998_ = lean_st_ref_take(v_a_977_);
v___x_999_ = lean_box(2);
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_998_, v_var_976_, v___x_999_);
v___x_1001_ = lean_st_ref_set(v_a_977_, v___x_1000_);
v___x_1002_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 0, v___x_1002_);
v___x_1004_ = v___x_983_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v___x_980_);
lean_dec(v_var_976_);
lean_dec(v_plannedDecision_975_);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_1009_, lean_object* v_var_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1009_, v_var_1010_, v_a_1011_);
lean_dec(v_a_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_1014_, lean_object* v_var_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1014_, v_var_1015_, v_a_1016_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_1024_, lean_object* v_var_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1024_, v_var_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec(v_a_1026_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_1034_, lean_object* v_m_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1035_, v_a_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1038_, v_m_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_m_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object* v_00_u03b2_1042_, lean_object* v_m_1043_, lean_object* v_a_1044_, lean_object* v_b_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_1043_, v_a_1044_, v_b_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object* v_00_u03b2_1047_, lean_object* v_a_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_a_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_1051_, v_a_1052_, v_x_1053_);
lean_dec(v_x_1053_);
lean_dec(v_a_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object* v_00_u03b2_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_1056_, v_b_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1060_, lean_object* v_f_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
switch(lean_obj_tag(v_alt_1060_))
{
case 0:
{
lean_object* v_code_1069_; lean_object* v___x_1070_; 
v_code_1069_ = lean_ctor_get(v_alt_1060_, 2);
lean_inc_ref(v_code_1069_);
lean_dec_ref_known(v_alt_1060_, 3);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc(v___y_1062_);
v___x_1070_ = lean_apply_8(v_f_1061_, v_code_1069_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
return v___x_1070_;
}
case 1:
{
lean_object* v_code_1071_; lean_object* v___x_1072_; 
v_code_1071_ = lean_ctor_get(v_alt_1060_, 1);
lean_inc_ref(v_code_1071_);
lean_dec_ref_known(v_alt_1060_, 2);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc(v___y_1062_);
v___x_1072_ = lean_apply_8(v_f_1061_, v_code_1071_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
return v___x_1072_;
}
default: 
{
lean_object* v_code_1073_; lean_object* v___x_1074_; 
v_code_1073_ = lean_ctor_get(v_alt_1060_, 0);
lean_inc_ref(v_code_1073_);
lean_dec_ref_known(v_alt_1060_, 1);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc(v___y_1062_);
v___x_1074_ = lean_apply_8(v_f_1061_, v_code_1073_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1075_, lean_object* v_f_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1075_, v_f_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v___y_1077_);
return v_res_1084_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_instMonadEIO(lean_box(0));
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_toApplicative_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1163_; 
v___x_1098_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1099_ = l_StateRefT_x27_instMonad___redArg(v___x_1098_);
v_toApplicative_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1099_, 1);
lean_dec(v_unused_1164_);
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1163_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_toApplicative_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1163_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_toFunctor_1104_; lean_object* v_toSeq_1105_; lean_object* v_toSeqLeft_1106_; lean_object* v_toSeqRight_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1161_; 
v_toFunctor_1104_ = lean_ctor_get(v_toApplicative_1100_, 0);
v_toSeq_1105_ = lean_ctor_get(v_toApplicative_1100_, 2);
v_toSeqLeft_1106_ = lean_ctor_get(v_toApplicative_1100_, 3);
v_toSeqRight_1107_ = lean_ctor_get(v_toApplicative_1100_, 4);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_toApplicative_1100_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_toApplicative_1100_, 1);
lean_dec(v_unused_1162_);
v___x_1109_ = v_toApplicative_1100_;
v_isShared_1110_ = v_isSharedCheck_1161_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_toSeqRight_1107_);
lean_inc(v_toSeqLeft_1106_);
lean_inc(v_toSeq_1105_);
lean_inc(v_toFunctor_1104_);
lean_dec(v_toApplicative_1100_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1161_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___f_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___x_1120_; 
v___f_1111_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1112_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1104_);
v___f_1113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1113_, 0, v_toFunctor_1104_);
v___f_1114_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1114_, 0, v_toFunctor_1104_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___f_1113_);
lean_ctor_set(v___x_1115_, 1, v___f_1114_);
v___f_1116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1116_, 0, v_toSeqRight_1107_);
v___f_1117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1117_, 0, v_toSeqLeft_1106_);
v___f_1118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1118_, 0, v_toSeq_1105_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v___f_1116_);
lean_ctor_set(v___x_1109_, 3, v___f_1117_);
lean_ctor_set(v___x_1109_, 2, v___f_1118_);
lean_ctor_set(v___x_1109_, 1, v___f_1111_);
lean_ctor_set(v___x_1109_, 0, v___x_1115_);
v___x_1120_ = v___x_1109_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___f_1111_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v___f_1118_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v___f_1117_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v___f_1116_);
v___x_1120_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___f_1112_);
lean_ctor_set(v___x_1102_, 0, v___x_1120_);
v___x_1122_ = v___x_1102_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___f_1112_);
v___x_1122_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v_toApplicative_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1157_; 
v___x_1123_ = l_StateRefT_x27_instMonad___redArg(v___x_1122_);
v_toApplicative_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v___x_1123_, 1);
lean_dec(v_unused_1158_);
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1157_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_toApplicative_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1157_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_toFunctor_1128_; lean_object* v_toSeq_1129_; lean_object* v_toSeqLeft_1130_; lean_object* v_toSeqRight_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_toFunctor_1128_ = lean_ctor_get(v_toApplicative_1124_, 0);
v_toSeq_1129_ = lean_ctor_get(v_toApplicative_1124_, 2);
v_toSeqLeft_1130_ = lean_ctor_get(v_toApplicative_1124_, 3);
v_toSeqRight_1131_ = lean_ctor_get(v_toApplicative_1124_, 4);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_toApplicative_1124_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_toApplicative_1124_, 1);
lean_dec(v_unused_1156_);
v___x_1133_ = v_toApplicative_1124_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_toSeqRight_1131_);
lean_inc(v_toSeqLeft_1130_);
lean_inc(v_toSeq_1129_);
lean_inc(v_toFunctor_1128_);
lean_dec(v_toApplicative_1124_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___x_1144_; 
v___f_1135_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1136_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1128_);
v___f_1137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1137_, 0, v_toFunctor_1128_);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1138_, 0, v_toFunctor_1128_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___f_1137_);
lean_ctor_set(v___x_1139_, 1, v___f_1138_);
v___f_1140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1140_, 0, v_toSeqRight_1131_);
v___f_1141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1141_, 0, v_toSeqLeft_1130_);
v___f_1142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1142_, 0, v_toSeq_1129_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 4, v___f_1140_);
lean_ctor_set(v___x_1133_, 3, v___f_1141_);
lean_ctor_set(v___x_1133_, 2, v___f_1142_);
lean_ctor_set(v___x_1133_, 1, v___f_1135_);
lean_ctor_set(v___x_1133_, 0, v___x_1139_);
v___x_1144_ = v___x_1133_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___f_1135_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v___f_1142_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v___f_1141_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v___f_1140_);
v___x_1144_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___f_1136_);
lean_ctor_set(v___x_1126_, 0, v___x_1144_);
v___x_1146_ = v___x_1126_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___f_1136_);
v___x_1146_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_9302__overap_1151_; lean_object* v___x_1152_; 
v___x_1147_ = l_ReaderT_instMonad___redArg(v___x_1146_);
v___x_1148_ = l_StateRefT_x27_instMonad___redArg(v___x_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = l_instInhabitedOfMonad___redArg(v___x_1148_, v___x_1149_);
v___x_9302__overap_1151_ = lean_panic_fn_borrowed(v___x_1150_, v_msg_1090_);
lean_dec(v___x_1150_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc(v___y_1091_);
v___x_1152_ = lean_apply_7(v___x_9302__overap_1151_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, lean_box(0));
return v___x_1152_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
return v_res_1173_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1177_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1178_ = lean_unsigned_to_nat(40u);
v___x_1179_ = lean_unsigned_to_nat(49u);
v___x_1180_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1181_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1182_ = l_mkPanicMessageWithDecl(v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_, v___x_1177_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1183_, lean_object* v_e_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_ty_1193_; lean_object* v_body_1194_; uint8_t v___x_1197_; 
v___x_1197_ = l_Lean_Expr_hasFVar(v_e_1184_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec_ref(v_e_1184_);
lean_dec_ref(v_f_1183_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
else
{
switch(lean_obj_tag(v_e_1184_))
{
case 1:
{
lean_object* v_fvarId_1200_; lean_object* v___x_1201_; 
v_fvarId_1200_ = lean_ctor_get(v_e_1184_, 0);
lean_inc(v_fvarId_1200_);
lean_dec_ref_known(v_e_1184_, 1);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc(v___y_1185_);
v___x_1201_ = lean_apply_8(v_f_1183_, v_fvarId_1200_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1201_;
}
case 2:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec_ref_known(v_e_1184_, 1);
lean_dec_ref(v_f_1183_);
v___x_1202_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1203_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1202_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1203_;
}
case 5:
{
lean_object* v_fn_1204_; lean_object* v_arg_1205_; lean_object* v___x_1206_; 
v_fn_1204_ = lean_ctor_get(v_e_1184_, 0);
lean_inc_ref(v_fn_1204_);
v_arg_1205_ = lean_ctor_get(v_e_1184_, 1);
lean_inc_ref(v_arg_1205_);
lean_dec_ref_known(v_e_1184_, 2);
lean_inc_ref(v_f_1183_);
v___x_1206_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1183_, v_fn_1204_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_dec_ref_known(v___x_1206_, 1);
v_e_1184_ = v_arg_1205_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1205_);
lean_dec_ref(v_f_1183_);
return v___x_1206_;
}
}
case 6:
{
lean_object* v_binderType_1208_; lean_object* v_body_1209_; 
v_binderType_1208_ = lean_ctor_get(v_e_1184_, 1);
lean_inc_ref(v_binderType_1208_);
v_body_1209_ = lean_ctor_get(v_e_1184_, 2);
lean_inc_ref(v_body_1209_);
lean_dec_ref_known(v_e_1184_, 3);
v_ty_1193_ = v_binderType_1208_;
v_body_1194_ = v_body_1209_;
goto v___jp_1192_;
}
case 7:
{
lean_object* v_binderType_1210_; lean_object* v_body_1211_; 
v_binderType_1210_ = lean_ctor_get(v_e_1184_, 1);
lean_inc_ref(v_binderType_1210_);
v_body_1211_ = lean_ctor_get(v_e_1184_, 2);
lean_inc_ref(v_body_1211_);
lean_dec_ref_known(v_e_1184_, 3);
v_ty_1193_ = v_binderType_1210_;
v_body_1194_ = v_body_1211_;
goto v___jp_1192_;
}
case 8:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref_known(v_e_1184_, 4);
lean_dec_ref(v_f_1183_);
v___x_1212_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1213_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1212_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1213_;
}
case 11:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref_known(v_e_1184_, 3);
lean_dec_ref(v_f_1183_);
v___x_1214_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1215_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1214_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1215_;
}
default: 
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_e_1184_);
lean_dec_ref(v_f_1183_);
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
}
v___jp_1192_:
{
lean_object* v___x_1195_; 
lean_inc_ref(v_f_1183_);
v___x_1195_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1183_, v_ty_1193_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_dec_ref_known(v___x_1195_, 1);
v_e_1184_ = v_body_1194_;
goto _start;
}
else
{
lean_dec_ref(v_body_1194_);
lean_dec_ref(v_f_1183_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1218_, lean_object* v_e_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1218_, v_e_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1220_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1228_, lean_object* v_param_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_type_1237_; lean_object* v___x_1238_; 
v_type_1237_ = lean_ctor_get(v_param_1229_, 2);
lean_inc_ref(v_type_1237_);
lean_dec_ref(v_param_1229_);
v___x_1238_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1228_, v_type_1237_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1239_, lean_object* v_param_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1239_, v_param_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1249_, lean_object* v_f_1250_, lean_object* v_as_1251_, size_t v_i_1252_, size_t v_stop_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_eq(v_i_1252_, v_stop_1253_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_array_uget_borrowed(v_as_1251_, v_i_1252_);
lean_inc(v___x_1263_);
lean_inc_ref(v_f_1250_);
v___x_1264_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1250_, v___x_1263_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; size_t v___x_1266_; size_t v___x_1267_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = ((size_t)1ULL);
v___x_1267_ = lean_usize_add(v_i_1252_, v___x_1266_);
v_i_1252_ = v___x_1267_;
v_b_1254_ = v_a_1265_;
goto _start;
}
else
{
lean_dec_ref(v_f_1250_);
return v___x_1264_;
}
}
else
{
lean_object* v___x_1269_; 
lean_dec_ref(v_f_1250_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_b_1254_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1270_, lean_object* v_f_1271_, lean_object* v_as_1272_, lean_object* v_i_1273_, lean_object* v_stop_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v_pu_boxed_1283_; size_t v_i_boxed_1284_; size_t v_stop_boxed_1285_; lean_object* v_res_1286_; 
v_pu_boxed_1283_ = lean_unbox(v_pu_1270_);
v_i_boxed_1284_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_stop_boxed_1285_ = lean_unbox_usize(v_stop_1274_);
lean_dec(v_stop_1274_);
v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1283_, v_f_1271_, v_as_1272_, v_i_boxed_1284_, v_stop_boxed_1285_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v_as_1272_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1287_, lean_object* v_arg_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
switch(lean_obj_tag(v_arg_1288_))
{
case 0:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v_f_1287_);
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
case 1:
{
lean_object* v_fvarId_1298_; lean_object* v___x_1299_; 
v_fvarId_1298_ = lean_ctor_get(v_arg_1288_, 0);
lean_inc(v_fvarId_1298_);
lean_dec_ref_known(v_arg_1288_, 1);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc(v___y_1289_);
v___x_1299_ = lean_apply_8(v_f_1287_, v_fvarId_1298_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, lean_box(0));
return v___x_1299_;
}
default: 
{
lean_object* v_expr_1300_; lean_object* v___x_1301_; 
v_expr_1300_ = lean_ctor_get(v_arg_1288_, 0);
lean_inc_ref(v_expr_1300_);
lean_dec_ref_known(v_arg_1288_, 1);
v___x_1301_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1287_, v_expr_1300_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1302_, lean_object* v_arg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1302_, v_arg_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec(v___y_1304_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1312_, lean_object* v_f_1313_, lean_object* v_as_1314_, size_t v_i_1315_, size_t v_stop_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_eq(v_i_1315_, v_stop_1316_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_array_uget_borrowed(v_as_1314_, v_i_1315_);
lean_inc(v___x_1326_);
lean_inc_ref(v_f_1313_);
v___x_1327_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1313_, v___x_1326_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; size_t v___x_1329_; size_t v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1315_, v___x_1329_);
v_i_1315_ = v___x_1330_;
v_b_1317_ = v_a_1328_;
goto _start;
}
else
{
lean_dec_ref(v_f_1313_);
return v___x_1327_;
}
}
else
{
lean_object* v___x_1332_; 
lean_dec_ref(v_f_1313_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_b_1317_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1333_, lean_object* v_f_1334_, lean_object* v_as_1335_, lean_object* v_i_1336_, lean_object* v_stop_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_pu_boxed_1346_; size_t v_i_boxed_1347_; size_t v_stop_boxed_1348_; lean_object* v_res_1349_; 
v_pu_boxed_1346_ = lean_unbox(v_pu_1333_);
v_i_boxed_1347_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_stop_boxed_1348_ = lean_unbox_usize(v_stop_1337_);
lean_dec(v_stop_1337_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1346_, v_f_1334_, v_as_1335_, v_i_boxed_1347_, v_stop_boxed_1348_, v_b_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v_as_1335_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1350_, lean_object* v_f_1351_, lean_object* v_e_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_args_1361_; 
switch(lean_obj_tag(v_e_1352_))
{
case 2:
{
lean_object* v_struct_1375_; lean_object* v___x_1376_; 
v_struct_1375_ = lean_ctor_get(v_e_1352_, 2);
lean_inc(v_struct_1375_);
lean_dec_ref_known(v_e_1352_, 3);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1376_ = lean_apply_8(v_f_1351_, v_struct_1375_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1376_;
}
case 3:
{
lean_object* v_args_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_args_1377_ = lean_ctor_get(v_e_1352_, 2);
lean_inc_ref(v_args_1377_);
lean_dec_ref_known(v_e_1352_, 3);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_array_get_size(v_args_1377_);
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_nat_dec_lt(v___x_1378_, v___x_1379_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref(v_args_1377_);
lean_dec_ref(v_f_1351_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
return v___x_1382_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_le(v___x_1379_, v___x_1379_);
if (v___x_1383_ == 0)
{
if (v___x_1381_ == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref(v_args_1377_);
lean_dec_ref(v_f_1351_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1380_);
return v___x_1384_;
}
else
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = lean_usize_of_nat(v___x_1379_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1377_, v___x_1385_, v___x_1386_, v___x_1380_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1377_);
return v___x_1387_;
}
}
else
{
size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = lean_usize_of_nat(v___x_1379_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1377_, v___x_1388_, v___x_1389_, v___x_1380_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1377_);
return v___x_1390_;
}
}
}
case 4:
{
lean_object* v_fvarId_1391_; lean_object* v_args_1392_; lean_object* v___x_1393_; 
v_fvarId_1391_ = lean_ctor_get(v_e_1352_, 0);
lean_inc(v_fvarId_1391_);
v_args_1392_ = lean_ctor_get(v_e_1352_, 1);
lean_inc_ref(v_args_1392_);
lean_dec_ref_known(v_e_1352_, 2);
lean_inc_ref(v_f_1351_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1393_ = lean_apply_8(v_f_1351_, v_fvarId_1391_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1414_; 
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1415_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1414_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1414_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_array_get_size(v_args_1392_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_nat_dec_lt(v___x_1397_, v___x_1398_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref(v_args_1392_);
lean_dec_ref(v_f_1351_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1402_ = v___x_1395_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1399_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_le(v___x_1398_, v___x_1398_);
if (v___x_1404_ == 0)
{
if (v___x_1400_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_args_1392_);
lean_dec_ref(v_f_1351_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1406_ = v___x_1395_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1399_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
lean_del_object(v___x_1395_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1398_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1392_, v___x_1408_, v___x_1409_, v___x_1399_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1392_);
return v___x_1410_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
lean_del_object(v___x_1395_);
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1398_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1392_, v___x_1411_, v___x_1412_, v___x_1399_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1392_);
return v___x_1413_;
}
}
}
}
else
{
lean_dec_ref(v_args_1392_);
lean_dec_ref(v_f_1351_);
return v___x_1393_;
}
}
case 5:
{
lean_object* v_args_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v_args_1416_ = lean_ctor_get(v_e_1352_, 1);
lean_inc_ref(v_args_1416_);
lean_dec_ref_known(v_e_1352_, 2);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_array_get_size(v_args_1416_);
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_args_1416_);
lean_dec_ref(v_f_1351_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
return v___x_1421_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_nat_dec_le(v___x_1418_, v___x_1418_);
if (v___x_1422_ == 0)
{
if (v___x_1420_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v_args_1416_);
lean_dec_ref(v_f_1351_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1419_);
return v___x_1423_;
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1418_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1416_, v___x_1424_, v___x_1425_, v___x_1419_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1416_);
return v___x_1426_;
}
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1418_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1416_, v___x_1427_, v___x_1428_, v___x_1419_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1416_);
return v___x_1429_;
}
}
}
case 6:
{
lean_object* v_var_1430_; lean_object* v___x_1431_; 
v_var_1430_ = lean_ctor_get(v_e_1352_, 1);
lean_inc(v_var_1430_);
lean_dec_ref_known(v_e_1352_, 2);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1431_ = lean_apply_8(v_f_1351_, v_var_1430_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1431_;
}
case 7:
{
lean_object* v_var_1432_; lean_object* v___x_1433_; 
v_var_1432_ = lean_ctor_get(v_e_1352_, 1);
lean_inc(v_var_1432_);
lean_dec_ref_known(v_e_1352_, 2);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1433_ = lean_apply_8(v_f_1351_, v_var_1432_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1433_;
}
case 8:
{
lean_object* v_var_1434_; lean_object* v___x_1435_; 
v_var_1434_ = lean_ctor_get(v_e_1352_, 2);
lean_inc(v_var_1434_);
lean_dec_ref_known(v_e_1352_, 3);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1435_ = lean_apply_8(v_f_1351_, v_var_1434_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1435_;
}
case 9:
{
lean_object* v_args_1436_; 
v_args_1436_ = lean_ctor_get(v_e_1352_, 1);
lean_inc_ref(v_args_1436_);
lean_dec_ref_known(v_e_1352_, 2);
v_args_1361_ = v_args_1436_;
goto v___jp_1360_;
}
case 10:
{
lean_object* v_args_1437_; 
v_args_1437_ = lean_ctor_get(v_e_1352_, 1);
lean_inc_ref(v_args_1437_);
lean_dec_ref_known(v_e_1352_, 2);
v_args_1361_ = v_args_1437_;
goto v___jp_1360_;
}
case 11:
{
lean_object* v_var_1438_; lean_object* v___x_1439_; 
v_var_1438_ = lean_ctor_get(v_e_1352_, 1);
lean_inc(v_var_1438_);
lean_dec_ref_known(v_e_1352_, 2);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1439_ = lean_apply_8(v_f_1351_, v_var_1438_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1439_;
}
case 12:
{
lean_object* v_var_1440_; lean_object* v_args_1441_; lean_object* v___x_1442_; 
v_var_1440_ = lean_ctor_get(v_e_1352_, 0);
lean_inc(v_var_1440_);
v_args_1441_ = lean_ctor_get(v_e_1352_, 2);
lean_inc_ref(v_args_1441_);
lean_dec_ref_known(v_e_1352_, 3);
lean_inc_ref(v_f_1351_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1442_ = lean_apply_8(v_f_1351_, v_var_1440_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1464_);
v___x_1444_ = v___x_1442_;
v_isShared_1445_ = v_isSharedCheck_1463_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v___x_1442_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1463_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_array_get_size(v_args_1441_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_nat_dec_lt(v___x_1446_, v___x_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref(v_args_1441_);
lean_dec_ref(v_f_1351_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1451_ = v___x_1444_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1448_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_nat_dec_le(v___x_1447_, v___x_1447_);
if (v___x_1453_ == 0)
{
if (v___x_1449_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref(v_args_1441_);
lean_dec_ref(v_f_1351_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1455_ = v___x_1444_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1448_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
else
{
size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
lean_del_object(v___x_1444_);
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = lean_usize_of_nat(v___x_1447_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1441_, v___x_1457_, v___x_1458_, v___x_1448_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1441_);
return v___x_1459_;
}
}
else
{
size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
lean_del_object(v___x_1444_);
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = lean_usize_of_nat(v___x_1447_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1441_, v___x_1460_, v___x_1461_, v___x_1448_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1441_);
return v___x_1462_;
}
}
}
}
else
{
lean_dec_ref(v_args_1441_);
lean_dec_ref(v_f_1351_);
return v___x_1442_;
}
}
case 13:
{
lean_object* v_fvarId_1465_; lean_object* v___x_1466_; 
v_fvarId_1465_ = lean_ctor_get(v_e_1352_, 1);
lean_inc(v_fvarId_1465_);
lean_dec_ref_known(v_e_1352_, 2);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1466_ = lean_apply_8(v_f_1351_, v_fvarId_1465_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1466_;
}
case 14:
{
lean_object* v_fvarId_1467_; lean_object* v___x_1468_; 
v_fvarId_1467_ = lean_ctor_get(v_e_1352_, 0);
lean_inc(v_fvarId_1467_);
lean_dec_ref_known(v_e_1352_, 1);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1468_ = lean_apply_8(v_f_1351_, v_fvarId_1467_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1468_;
}
case 15:
{
lean_object* v_fvarId_1469_; lean_object* v___x_1470_; 
v_fvarId_1469_ = lean_ctor_get(v_e_1352_, 0);
lean_inc(v_fvarId_1469_);
lean_dec_ref_known(v_e_1352_, 1);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc(v___y_1353_);
v___x_1470_ = lean_apply_8(v_f_1351_, v_fvarId_1469_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1470_;
}
default: 
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v_e_1352_);
lean_dec_ref(v_f_1351_);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_array_get_size(v_args_1361_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v_args_1361_);
lean_dec_ref(v_f_1351_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
return v___x_1366_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_nat_dec_le(v___x_1363_, v___x_1363_);
if (v___x_1367_ == 0)
{
if (v___x_1365_ == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref(v_args_1361_);
lean_dec_ref(v_f_1351_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1364_);
return v___x_1368_;
}
else
{
size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1363_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1361_, v___x_1369_, v___x_1370_, v___x_1364_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1361_);
return v___x_1371_;
}
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1363_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1350_, v_f_1351_, v_args_1361_, v___x_1372_, v___x_1373_, v___x_1364_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v_args_1361_);
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1473_, lean_object* v_f_1474_, lean_object* v_e_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_pu_boxed_1483_; lean_object* v_res_1484_; 
v_pu_boxed_1483_ = lean_unbox(v_pu_1473_);
v_res_1484_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1483_, v_f_1474_, v_e_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec(v___y_1476_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1485_, lean_object* v_f_1486_, lean_object* v_decl_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_type_1495_; lean_object* v_value_1496_; lean_object* v___x_1497_; 
v_type_1495_ = lean_ctor_get(v_decl_1487_, 2);
lean_inc_ref(v_type_1495_);
v_value_1496_ = lean_ctor_get(v_decl_1487_, 3);
lean_inc(v_value_1496_);
lean_dec_ref(v_decl_1487_);
lean_inc_ref(v_f_1486_);
v___x_1497_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1486_, v_type_1495_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref_known(v___x_1497_, 1);
v___x_1498_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1485_, v_f_1486_, v_value_1496_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1498_;
}
else
{
lean_dec(v_value_1496_);
lean_dec_ref(v_f_1486_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1499_, lean_object* v_f_1500_, lean_object* v_decl_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_pu_boxed_1509_; lean_object* v_res_1510_; 
v_pu_boxed_1509_ = lean_unbox(v_pu_1499_);
v_res_1510_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1509_, v_f_1500_, v_decl_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec(v___y_1502_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1511_, lean_object* v_f_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_pu_boxed_1521_; lean_object* v_res_1522_; 
v_pu_boxed_1521_ = lean_unbox(v_pu_1511_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1521_, v_f_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec(v___y_1514_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1523_, lean_object* v_f_1524_, lean_object* v_as_1525_, size_t v_i_1526_, size_t v_stop_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_eq(v_i_1526_, v_stop_1527_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___f_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_box(v_pu_1523_);
lean_inc_ref(v_f_1524_);
v___f_1538_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1538_, 0, v___x_1537_);
lean_closure_set(v___f_1538_, 1, v_f_1524_);
v___x_1539_ = lean_array_uget_borrowed(v_as_1525_, v_i_1526_);
lean_inc(v___x_1539_);
v___x_1540_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1539_, v___f_1538_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; size_t v___x_1542_; size_t v___x_1543_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_add(v_i_1526_, v___x_1542_);
v_i_1526_ = v___x_1543_;
v_b_1528_ = v_a_1541_;
goto _start;
}
else
{
lean_dec_ref(v_f_1524_);
return v___x_1540_;
}
}
else
{
lean_object* v___x_1545_; 
lean_dec_ref(v_f_1524_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_b_1528_);
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1546_, lean_object* v_f_1547_, lean_object* v_c_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
switch(lean_obj_tag(v_c_1548_))
{
case 0:
{
lean_object* v_decl_1556_; lean_object* v_k_1557_; lean_object* v___x_1558_; 
v_decl_1556_ = lean_ctor_get(v_c_1548_, 0);
lean_inc_ref(v_decl_1556_);
v_k_1557_ = lean_ctor_get(v_c_1548_, 1);
lean_inc_ref(v_k_1557_);
lean_dec_ref_known(v_c_1548_, 2);
lean_inc_ref(v_f_1547_);
v___x_1558_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1546_, v_f_1547_, v_decl_1556_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref_known(v___x_1558_, 1);
v_c_1548_ = v_k_1557_;
goto _start;
}
else
{
lean_dec_ref(v_k_1557_);
lean_dec_ref(v_f_1547_);
return v___x_1558_;
}
}
case 3:
{
lean_object* v_fvarId_1560_; lean_object* v_args_1561_; lean_object* v___x_1562_; 
v_fvarId_1560_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1560_);
v_args_1561_ = lean_ctor_get(v_c_1548_, 1);
lean_inc_ref(v_args_1561_);
lean_dec_ref_known(v_c_1548_, 2);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1562_ = lean_apply_8(v_f_1547_, v_fvarId_1560_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1562_, 0);
lean_dec(v_unused_1584_);
v___x_1564_ = v___x_1562_;
v_isShared_1565_ = v_isSharedCheck_1583_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v___x_1562_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1583_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = lean_array_get_size(v_args_1561_);
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_nat_dec_lt(v___x_1566_, v___x_1567_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref(v_args_1561_);
lean_dec_ref(v_f_1547_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1568_);
v___x_1571_ = v___x_1564_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1568_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
else
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_le(v___x_1567_, v___x_1567_);
if (v___x_1573_ == 0)
{
if (v___x_1569_ == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v_args_1561_);
lean_dec_ref(v_f_1547_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1568_);
v___x_1575_ = v___x_1564_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1568_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1564_);
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = lean_usize_of_nat(v___x_1567_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1546_, v_f_1547_, v_args_1561_, v___x_1577_, v___x_1578_, v___x_1568_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_args_1561_);
return v___x_1579_;
}
}
else
{
size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
lean_del_object(v___x_1564_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1567_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1546_, v_f_1547_, v_args_1561_, v___x_1580_, v___x_1581_, v___x_1568_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_args_1561_);
return v___x_1582_;
}
}
}
}
else
{
lean_dec_ref(v_args_1561_);
lean_dec_ref(v_f_1547_);
return v___x_1562_;
}
}
case 4:
{
lean_object* v_cases_1585_; lean_object* v_resultType_1586_; lean_object* v_discr_1587_; lean_object* v_alts_1588_; lean_object* v___x_1589_; 
v_cases_1585_ = lean_ctor_get(v_c_1548_, 0);
lean_inc_ref(v_cases_1585_);
lean_dec_ref_known(v_c_1548_, 1);
v_resultType_1586_ = lean_ctor_get(v_cases_1585_, 1);
lean_inc_ref(v_resultType_1586_);
v_discr_1587_ = lean_ctor_get(v_cases_1585_, 2);
lean_inc(v_discr_1587_);
v_alts_1588_ = lean_ctor_get(v_cases_1585_, 3);
lean_inc_ref(v_alts_1588_);
lean_dec_ref(v_cases_1585_);
lean_inc_ref(v_f_1547_);
v___x_1589_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1547_, v_resultType_1586_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref_known(v___x_1589_, 1);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1590_ = lean_apply_8(v_f_1547_, v_discr_1587_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1611_; 
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1590_, 0);
lean_dec(v_unused_1612_);
v___x_1592_ = v___x_1590_;
v_isShared_1593_ = v_isSharedCheck_1611_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v___x_1590_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1611_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_array_get_size(v_alts_1588_);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_nat_dec_lt(v___x_1594_, v___x_1595_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref(v_alts_1588_);
lean_dec_ref(v_f_1547_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1596_);
v___x_1599_ = v___x_1592_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1596_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
else
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_nat_dec_le(v___x_1595_, v___x_1595_);
if (v___x_1601_ == 0)
{
if (v___x_1597_ == 0)
{
lean_object* v___x_1603_; 
lean_dec_ref(v_alts_1588_);
lean_dec_ref(v_f_1547_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1596_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1596_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
else
{
size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1592_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = lean_usize_of_nat(v___x_1595_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1546_, v_f_1547_, v_alts_1588_, v___x_1605_, v___x_1606_, v___x_1596_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_alts_1588_);
return v___x_1607_;
}
}
else
{
size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
lean_del_object(v___x_1592_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = lean_usize_of_nat(v___x_1595_);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1546_, v_f_1547_, v_alts_1588_, v___x_1608_, v___x_1609_, v___x_1596_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_alts_1588_);
return v___x_1610_;
}
}
}
}
else
{
lean_dec_ref(v_alts_1588_);
lean_dec_ref(v_f_1547_);
return v___x_1590_;
}
}
else
{
lean_dec_ref(v_alts_1588_);
lean_dec(v_discr_1587_);
lean_dec_ref(v_f_1547_);
return v___x_1589_;
}
}
case 5:
{
lean_object* v_fvarId_1613_; lean_object* v___x_1614_; 
v_fvarId_1613_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1613_);
lean_dec_ref_known(v_c_1548_, 1);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1614_ = lean_apply_8(v_f_1547_, v_fvarId_1613_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
return v___x_1614_;
}
case 6:
{
lean_object* v_type_1615_; lean_object* v___x_1616_; 
v_type_1615_ = lean_ctor_get(v_c_1548_, 0);
lean_inc_ref(v_type_1615_);
lean_dec_ref_known(v_c_1548_, 1);
v___x_1616_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1547_, v_type_1615_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1616_;
}
case 7:
{
lean_object* v_fvarId_1617_; lean_object* v_y_1618_; lean_object* v_k_1619_; lean_object* v___x_1620_; 
v_fvarId_1617_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1617_);
v_y_1618_ = lean_ctor_get(v_c_1548_, 2);
lean_inc(v_y_1618_);
v_k_1619_ = lean_ctor_get(v_c_1548_, 3);
lean_inc_ref(v_k_1619_);
lean_dec_ref_known(v_c_1548_, 4);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1620_ = lean_apply_8(v_f_1547_, v_fvarId_1617_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1621_; 
lean_dec_ref_known(v___x_1620_, 1);
lean_inc_ref(v_f_1547_);
v___x_1621_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1547_, v_y_1618_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_dec_ref_known(v___x_1621_, 1);
v_c_1548_ = v_k_1619_;
goto _start;
}
else
{
lean_dec_ref(v_k_1619_);
lean_dec_ref(v_f_1547_);
return v___x_1621_;
}
}
else
{
lean_dec_ref(v_k_1619_);
lean_dec(v_y_1618_);
lean_dec_ref(v_f_1547_);
return v___x_1620_;
}
}
case 8:
{
lean_object* v_fvarId_1623_; lean_object* v_y_1624_; lean_object* v_k_1625_; lean_object* v___x_1626_; 
v_fvarId_1623_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1623_);
v_y_1624_ = lean_ctor_get(v_c_1548_, 2);
lean_inc(v_y_1624_);
v_k_1625_ = lean_ctor_get(v_c_1548_, 3);
lean_inc_ref(v_k_1625_);
lean_dec_ref_known(v_c_1548_, 4);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1626_ = lean_apply_8(v_f_1547_, v_fvarId_1623_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v___x_1627_; 
lean_dec_ref_known(v___x_1626_, 1);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1627_ = lean_apply_8(v_f_1547_, v_y_1624_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
v_c_1548_ = v_k_1625_;
goto _start;
}
else
{
lean_dec_ref(v_k_1625_);
lean_dec_ref(v_f_1547_);
return v___x_1627_;
}
}
else
{
lean_dec_ref(v_k_1625_);
lean_dec(v_y_1624_);
lean_dec_ref(v_f_1547_);
return v___x_1626_;
}
}
case 9:
{
lean_object* v_fvarId_1629_; lean_object* v_y_1630_; lean_object* v_ty_1631_; lean_object* v_k_1632_; lean_object* v___x_1633_; 
v_fvarId_1629_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1629_);
v_y_1630_ = lean_ctor_get(v_c_1548_, 3);
lean_inc(v_y_1630_);
v_ty_1631_ = lean_ctor_get(v_c_1548_, 4);
lean_inc_ref(v_ty_1631_);
v_k_1632_ = lean_ctor_get(v_c_1548_, 5);
lean_inc_ref(v_k_1632_);
lean_dec_ref_known(v_c_1548_, 6);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1633_ = lean_apply_8(v_f_1547_, v_fvarId_1629_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1633_, 1);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1634_ = lean_apply_8(v_f_1547_, v_y_1630_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref_known(v___x_1634_, 1);
lean_inc_ref(v_f_1547_);
v___x_1635_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1547_, v_ty_1631_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec_ref_known(v___x_1635_, 1);
v_c_1548_ = v_k_1632_;
goto _start;
}
else
{
lean_dec_ref(v_k_1632_);
lean_dec_ref(v_f_1547_);
return v___x_1635_;
}
}
else
{
lean_dec_ref(v_k_1632_);
lean_dec_ref(v_ty_1631_);
lean_dec_ref(v_f_1547_);
return v___x_1634_;
}
}
else
{
lean_dec_ref(v_k_1632_);
lean_dec_ref(v_ty_1631_);
lean_dec(v_y_1630_);
lean_dec_ref(v_f_1547_);
return v___x_1633_;
}
}
case 10:
{
lean_object* v_fvarId_1637_; lean_object* v_k_1638_; lean_object* v___x_1639_; 
v_fvarId_1637_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1637_);
v_k_1638_ = lean_ctor_get(v_c_1548_, 2);
lean_inc_ref(v_k_1638_);
lean_dec_ref_known(v_c_1548_, 3);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1639_ = lean_apply_8(v_f_1547_, v_fvarId_1637_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref_known(v___x_1639_, 1);
v_c_1548_ = v_k_1638_;
goto _start;
}
else
{
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_f_1547_);
return v___x_1639_;
}
}
case 11:
{
lean_object* v_fvarId_1641_; lean_object* v_k_1642_; lean_object* v___x_1643_; 
v_fvarId_1641_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1641_);
v_k_1642_ = lean_ctor_get(v_c_1548_, 2);
lean_inc_ref(v_k_1642_);
lean_dec_ref_known(v_c_1548_, 3);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1643_ = lean_apply_8(v_f_1547_, v_fvarId_1641_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_dec_ref_known(v___x_1643_, 1);
v_c_1548_ = v_k_1642_;
goto _start;
}
else
{
lean_dec_ref(v_k_1642_);
lean_dec_ref(v_f_1547_);
return v___x_1643_;
}
}
case 12:
{
lean_object* v_fvarId_1645_; lean_object* v_k_1646_; lean_object* v___x_1647_; 
v_fvarId_1645_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1645_);
v_k_1646_ = lean_ctor_get(v_c_1548_, 3);
lean_inc_ref(v_k_1646_);
lean_dec_ref_known(v_c_1548_, 4);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1647_ = lean_apply_8(v_f_1547_, v_fvarId_1645_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref_known(v___x_1647_, 1);
v_c_1548_ = v_k_1646_;
goto _start;
}
else
{
lean_dec_ref(v_k_1646_);
lean_dec_ref(v_f_1547_);
return v___x_1647_;
}
}
case 13:
{
lean_object* v_fvarId_1649_; lean_object* v_k_1650_; lean_object* v___x_1651_; 
v_fvarId_1649_ = lean_ctor_get(v_c_1548_, 0);
lean_inc(v_fvarId_1649_);
v_k_1650_ = lean_ctor_get(v_c_1548_, 1);
lean_inc_ref(v_k_1650_);
lean_dec_ref_known(v_c_1548_, 2);
lean_inc_ref(v_f_1547_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc_ref(v___y_1551_);
lean_inc(v___y_1550_);
lean_inc(v___y_1549_);
v___x_1651_ = lean_apply_8(v_f_1547_, v_fvarId_1649_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_dec_ref_known(v___x_1651_, 1);
v_c_1548_ = v_k_1650_;
goto _start;
}
else
{
lean_dec_ref(v_k_1650_);
lean_dec_ref(v_f_1547_);
return v___x_1651_;
}
}
default: 
{
lean_object* v_decl_1653_; lean_object* v_k_1654_; lean_object* v_params_1655_; lean_object* v_type_1656_; lean_object* v_value_1657_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_decl_1653_ = lean_ctor_get(v_c_1548_, 0);
lean_inc_ref(v_decl_1653_);
v_k_1654_ = lean_ctor_get(v_c_1548_, 1);
lean_inc_ref(v_k_1654_);
lean_dec_ref(v_c_1548_);
v_params_1655_ = lean_ctor_get(v_decl_1653_, 2);
lean_inc_ref(v_params_1655_);
v_type_1656_ = lean_ctor_get(v_decl_1653_, 3);
lean_inc_ref(v_type_1656_);
v_value_1657_ = lean_ctor_get(v_decl_1653_, 4);
lean_inc_ref(v_value_1657_);
lean_dec_ref(v_decl_1653_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_array_get_size(v_params_1655_);
v___x_1670_ = lean_nat_dec_lt(v___x_1668_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref(v_params_1655_);
lean_inc_ref(v_f_1547_);
v___x_1671_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1547_, v_type_1656_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref_known(v___x_1671_, 1);
lean_inc_ref(v_f_1547_);
v___x_1672_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1546_, v_f_1547_, v_value_1657_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_dec_ref_known(v___x_1672_, 1);
v_c_1548_ = v_k_1654_;
goto _start;
}
else
{
lean_dec_ref(v_k_1654_);
lean_dec_ref(v_f_1547_);
return v___x_1672_;
}
}
else
{
lean_dec_ref(v_value_1657_);
lean_dec_ref(v_k_1654_);
lean_dec_ref(v_f_1547_);
return v___x_1671_;
}
}
else
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_nat_dec_le(v___x_1669_, v___x_1669_);
if (v___x_1675_ == 0)
{
if (v___x_1670_ == 0)
{
lean_dec_ref(v_params_1655_);
v___y_1659_ = v___y_1549_;
v___y_1660_ = v___y_1550_;
v___y_1661_ = v___y_1551_;
v___y_1662_ = v___y_1552_;
v___y_1663_ = v___y_1553_;
v___y_1664_ = v___y_1554_;
goto v___jp_1658_;
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_of_nat(v___x_1669_);
lean_inc_ref(v_f_1547_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1546_, v_f_1547_, v_params_1655_, v___x_1676_, v___x_1677_, v___x_1674_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_params_1655_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref_known(v___x_1678_, 1);
v___y_1659_ = v___y_1549_;
v___y_1660_ = v___y_1550_;
v___y_1661_ = v___y_1551_;
v___y_1662_ = v___y_1552_;
v___y_1663_ = v___y_1553_;
v___y_1664_ = v___y_1554_;
goto v___jp_1658_;
}
else
{
lean_dec_ref(v_value_1657_);
lean_dec_ref(v_type_1656_);
lean_dec_ref(v_k_1654_);
lean_dec_ref(v_f_1547_);
return v___x_1678_;
}
}
}
else
{
size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = lean_usize_of_nat(v___x_1669_);
lean_inc_ref(v_f_1547_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1546_, v_f_1547_, v_params_1655_, v___x_1679_, v___x_1680_, v___x_1674_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_params_1655_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_dec_ref_known(v___x_1681_, 1);
v___y_1659_ = v___y_1549_;
v___y_1660_ = v___y_1550_;
v___y_1661_ = v___y_1551_;
v___y_1662_ = v___y_1552_;
v___y_1663_ = v___y_1553_;
v___y_1664_ = v___y_1554_;
goto v___jp_1658_;
}
else
{
lean_dec_ref(v_value_1657_);
lean_dec_ref(v_type_1656_);
lean_dec_ref(v_k_1654_);
lean_dec_ref(v_f_1547_);
return v___x_1681_;
}
}
}
v___jp_1658_:
{
lean_object* v___x_1665_; 
lean_inc_ref(v_f_1547_);
v___x_1665_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1547_, v_type_1656_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref_known(v___x_1665_, 1);
lean_inc_ref(v_f_1547_);
v___x_1666_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1546_, v_f_1547_, v_value_1657_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_dec_ref_known(v___x_1666_, 1);
v_c_1548_ = v_k_1654_;
v___y_1549_ = v___y_1659_;
v___y_1550_ = v___y_1660_;
v___y_1551_ = v___y_1661_;
v___y_1552_ = v___y_1662_;
v___y_1553_ = v___y_1663_;
v___y_1554_ = v___y_1664_;
goto _start;
}
else
{
lean_dec_ref(v_k_1654_);
lean_dec_ref(v_f_1547_);
return v___x_1666_;
}
}
else
{
lean_dec_ref(v_value_1657_);
lean_dec_ref(v_k_1654_);
lean_dec_ref(v_f_1547_);
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1682_, lean_object* v_f_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1682_, v_f_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1693_, lean_object* v_f_1694_, lean_object* v_as_1695_, lean_object* v_i_1696_, lean_object* v_stop_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v_pu_boxed_1706_; size_t v_i_boxed_1707_; size_t v_stop_boxed_1708_; lean_object* v_res_1709_; 
v_pu_boxed_1706_ = lean_unbox(v_pu_1693_);
v_i_boxed_1707_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_stop_boxed_1708_ = lean_unbox_usize(v_stop_1697_);
lean_dec(v_stop_1697_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1706_, v_f_1694_, v_as_1695_, v_i_boxed_1707_, v_stop_boxed_1708_, v_b_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v_as_1695_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1710_, lean_object* v_f_1711_, lean_object* v_c_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v_pu_boxed_1720_; lean_object* v_res_1721_; 
v_pu_boxed_1720_ = lean_unbox(v_pu_1710_);
v_res_1721_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1720_, v_f_1711_, v_c_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1722_, lean_object* v_as_1723_, size_t v_i_1724_, size_t v_stop_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_eq(v_i_1724_, v_stop_1725_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc(v___x_1722_);
v___x_1735_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1735_, 0, v___x_1722_);
v___x_1736_ = lean_array_uget_borrowed(v_as_1723_, v_i_1724_);
lean_inc(v___x_1736_);
v___x_1737_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1735_, v___x_1736_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; size_t v___x_1739_; size_t v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1724_, v___x_1739_);
v_i_1724_ = v___x_1740_;
v_b_1726_ = v_a_1738_;
goto _start;
}
else
{
lean_dec(v___x_1722_);
return v___x_1737_;
}
}
else
{
lean_object* v___x_1742_; 
lean_dec(v___x_1722_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_b_1726_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1743_, lean_object* v_as_1744_, lean_object* v_i_1745_, lean_object* v_stop_1746_, lean_object* v_b_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
size_t v_i_boxed_1755_; size_t v_stop_boxed_1756_; lean_object* v_res_1757_; 
v_i_boxed_1755_ = lean_unbox_usize(v_i_1745_);
lean_dec(v_i_1745_);
v_stop_boxed_1756_ = lean_unbox_usize(v_stop_1746_);
lean_dec(v_stop_1746_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1743_, v_as_1744_, v_i_boxed_1755_, v_stop_boxed_1756_, v_b_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v_as_1744_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = 0;
v___x_1767_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1758_);
lean_inc(v___x_1767_);
v___x_1768_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1768_, 0, v___x_1767_);
switch(lean_obj_tag(v_alt_1758_))
{
case 0:
{
lean_object* v_params_1769_; lean_object* v_code_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_params_1769_ = lean_ctor_get(v_alt_1758_, 1);
lean_inc_ref(v_params_1769_);
v_code_1770_ = lean_ctor_get(v_alt_1758_, 2);
lean_inc_ref(v_code_1770_);
lean_dec_ref_known(v_alt_1758_, 3);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_array_get_size(v_params_1769_);
v___x_1773_ = lean_nat_dec_lt(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v_params_1769_);
lean_dec(v___x_1767_);
v___x_1774_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1766_, v___x_1768_, v_code_1770_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_nat_dec_le(v___x_1772_, v___x_1772_);
if (v___x_1776_ == 0)
{
if (v___x_1773_ == 0)
{
lean_object* v___x_1777_; 
lean_dec_ref(v_params_1769_);
lean_dec(v___x_1767_);
v___x_1777_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1766_, v___x_1768_, v_code_1770_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1777_;
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_of_nat(v___x_1772_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1767_, v_params_1769_, v___x_1778_, v___x_1779_, v___x_1775_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec_ref(v_params_1769_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; 
lean_dec_ref_known(v___x_1780_, 1);
v___x_1781_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1766_, v___x_1768_, v_code_1770_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1781_;
}
else
{
lean_dec_ref(v_code_1770_);
lean_dec_ref(v___x_1768_);
return v___x_1780_;
}
}
}
else
{
size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = ((size_t)0ULL);
v___x_1783_ = lean_usize_of_nat(v___x_1772_);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1767_, v_params_1769_, v___x_1782_, v___x_1783_, v___x_1775_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec_ref(v_params_1769_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v___x_1785_; 
lean_dec_ref_known(v___x_1784_, 1);
v___x_1785_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1766_, v___x_1768_, v_code_1770_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1785_;
}
else
{
lean_dec_ref(v_code_1770_);
lean_dec_ref(v___x_1768_);
return v___x_1784_;
}
}
}
}
case 1:
{
lean_object* v_code_1786_; lean_object* v___x_1787_; 
lean_dec(v___x_1767_);
v_code_1786_ = lean_ctor_get(v_alt_1758_, 1);
lean_inc_ref(v_code_1786_);
lean_dec_ref_known(v_alt_1758_, 2);
v___x_1787_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1766_, v___x_1768_, v_code_1786_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1787_;
}
default: 
{
lean_object* v_code_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1767_);
v_code_1788_ = lean_ctor_get(v_alt_1758_, 0);
lean_inc_ref(v_code_1788_);
lean_dec_ref_known(v_alt_1758_, 1);
v___x_1789_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1766_, v___x_1768_, v_code_1788_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec(v_a_1791_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1799_, lean_object* v_f_1800_, lean_object* v_param_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1800_, v_param_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1810_, lean_object* v_f_1811_, lean_object* v_param_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v_pu_boxed_1820_; lean_object* v_res_1821_; 
v_pu_boxed_1820_ = lean_unbox(v_pu_1810_);
v_res_1821_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1820_, v_f_1811_, v_param_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec(v___y_1813_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1822_, lean_object* v_alt_1823_, lean_object* v_f_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1823_, v_f_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1833_, lean_object* v_alt_1834_, lean_object* v_f_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v_pu_boxed_1843_; lean_object* v_res_1844_; 
v_pu_boxed_1843_ = lean_unbox(v_pu_1833_);
v_res_1844_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1843_, v_alt_1834_, v_f_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec(v___y_1836_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1845_, lean_object* v_f_1846_, lean_object* v_arg_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1846_, v_arg_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1856_, lean_object* v_f_1857_, lean_object* v_arg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v_pu_boxed_1866_; lean_object* v_res_1867_; 
v_pu_boxed_1866_ = lean_unbox(v_pu_1856_);
v_res_1867_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1866_, v_f_1857_, v_arg_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec(v___y_1859_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1868_, size_t v_i_1869_, size_t v_stop_1870_, lean_object* v_b_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_usize_dec_eq(v_i_1869_, v_stop_1870_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_array_uget_borrowed(v_as_1868_, v_i_1869_);
lean_inc(v___x_1880_);
v___x_1881_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1880_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; size_t v___x_1883_; size_t v___x_1884_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_add(v_i_1869_, v___x_1883_);
v_i_1869_ = v___x_1884_;
v_b_1871_ = v_a_1882_;
goto _start;
}
else
{
return v___x_1881_;
}
}
else
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_b_1871_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1887_, lean_object* v_i_1888_, lean_object* v_stop_1889_, lean_object* v_b_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
size_t v_i_boxed_1898_; size_t v_stop_boxed_1899_; lean_object* v_res_1900_; 
v_i_boxed_1898_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_stop_boxed_1899_ = lean_unbox_usize(v_stop_1889_);
lean_dec(v_stop_1889_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1887_, v_i_boxed_1898_, v_stop_boxed_1899_, v_b_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v_as_1887_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_alts_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_alts_1909_ = lean_ctor_get(v_cs_1901_, 3);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_array_get_size(v_alts_1909_);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_nat_dec_lt(v___x_1910_, v___x_1911_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
return v___x_1914_;
}
else
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_nat_dec_le(v___x_1911_, v___x_1911_);
if (v___x_1915_ == 0)
{
if (v___x_1913_ == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1912_);
return v___x_1916_;
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = lean_usize_of_nat(v___x_1911_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1909_, v___x_1917_, v___x_1918_, v___x_1912_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1919_;
}
}
else
{
size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = lean_usize_of_nat(v___x_1911_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1909_, v___x_1920_, v___x_1921_, v___x_1912_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_cs_1923_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_x_1932_);
return v___x_1939_;
}
else
{
lean_object* v_head_1940_; lean_object* v_tail_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_2003_; 
v_head_1940_ = lean_ctor_get(v_x_1933_, 0);
v_tail_1941_ = lean_ctor_get(v_x_1933_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1943_ = v_x_1933_;
v_isShared_1944_ = v_isSharedCheck_2003_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_tail_1941_);
lean_inc(v_head_1940_);
lean_dec(v_x_1933_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_2003_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_fst_1945_; lean_object* v_snd_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_2002_; 
v_fst_1945_ = lean_ctor_get(v_x_1932_, 0);
v_snd_1946_ = lean_ctor_get(v_x_1932_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1948_ = v_x_1932_;
v_isShared_1949_ = v_isSharedCheck_2002_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snd_1946_);
lean_inc(v_fst_1945_);
lean_dec(v_x_1932_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_2002_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; 
if (lean_obj_tag(v_head_1940_) == 0)
{
lean_object* v_decl_1983_; lean_object* v___x_1984_; 
v_decl_1983_ = lean_ctor_get(v_head_1940_, 0);
lean_inc_ref(v_decl_1983_);
v___x_1984_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_1983_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; uint8_t v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1986_ == 0)
{
lean_del_object(v___x_1943_);
v___y_1951_ = v___y_1934_;
v___y_1952_ = v___y_1935_;
v___y_1953_ = v___y_1936_;
v___y_1954_ = v___y_1937_;
goto v___jp_1950_;
}
else
{
lean_object* v_fvarId_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_inc_ref(v_decl_1983_);
lean_dec_ref_known(v_head_1940_, 1);
lean_del_object(v___x_1948_);
v_fvarId_1987_ = lean_ctor_get(v_decl_1983_, 0);
lean_inc(v_fvarId_1987_);
lean_dec_ref(v_decl_1983_);
v___x_1988_ = lean_box(2);
v___x_1989_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1945_, v_fvarId_1987_, v___x_1988_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 0);
lean_ctor_set(v___x_1943_, 1, v_snd_1946_);
lean_ctor_set(v___x_1943_, 0, v___x_1989_);
v___x_1991_ = v___x_1943_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_snd_1946_);
v___x_1991_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
v_x_1932_ = v___x_1991_;
v_x_1933_ = v_tail_1941_;
goto _start;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref_known(v_head_1940_, 1);
lean_del_object(v___x_1948_);
lean_dec(v_snd_1946_);
lean_dec(v_fst_1945_);
lean_del_object(v___x_1943_);
lean_dec(v_tail_1941_);
v_a_1994_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1984_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1984_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_del_object(v___x_1943_);
v___y_1951_ = v___y_1934_;
v___y_1952_ = v___y_1935_;
v___y_1953_ = v___y_1936_;
v___y_1954_ = v___y_1937_;
goto v___jp_1950_;
}
v___jp_1950_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = lean_st_ref_get(v___y_1954_);
lean_dec(v___x_1955_);
v___x_1956_ = lean_st_mk_ref(v_snd_1946_);
lean_inc(v_head_1940_);
v___x_1957_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1940_, v___x_1956_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = lean_st_ref_get(v___x_1956_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_unbox(v_a_1958_);
lean_dec(v_a_1958_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1961_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1940_);
lean_dec(v_head_1940_);
v___x_1962_ = lean_box(3);
v___x_1963_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1945_, v___x_1961_, v___x_1962_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1959_);
lean_ctor_set(v___x_1948_, 0, v___x_1963_);
v___x_1965_ = v___x_1948_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___x_1959_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
v_x_1932_ = v___x_1965_;
v_x_1933_ = v_tail_1941_;
goto _start;
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1968_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1940_);
lean_dec(v_head_1940_);
v___x_1969_ = lean_box(2);
v___x_1970_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1945_, v___x_1968_, v___x_1969_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1959_);
lean_ctor_set(v___x_1948_, 0, v___x_1970_);
v___x_1972_ = v___x_1948_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1959_);
v___x_1972_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v_x_1932_ = v___x_1972_;
v_x_1933_ = v_tail_1941_;
goto _start;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v___x_1956_);
lean_del_object(v___x_1948_);
lean_dec(v_fst_1945_);
lean_dec(v_tail_1941_);
lean_dec(v_head_1940_);
v_a_1975_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1957_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1957_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2004_, v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2011_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_unsigned_to_nat(16u);
v___x_2014_ = lean_mk_array(v___x_2013_, v___x_2012_);
return v___x_2014_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v___x_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_map_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2051_ = l_List_lengthTR___redArg(v_a_2019_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_unsigned_to_nat(4u);
v___x_2054_ = lean_nat_mul(v___x_2051_, v___x_2053_);
lean_dec(v___x_2051_);
v___x_2055_ = lean_unsigned_to_nat(3u);
v___x_2056_ = lean_nat_div(v___x_2054_, v___x_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = l_Nat_nextPowerOfTwo(v___x_2056_);
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_mk_array(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2052_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_inc(v_a_2019_);
v___x_2063_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2062_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v_fst_2065_; lean_object* v_discr_2066_; uint8_t v___x_2067_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v_fst_2065_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_fst_2065_);
lean_dec(v_a_2064_);
v_discr_2066_ = lean_ctor_get(v_cs_2018_, 2);
v___x_2067_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2065_, v_discr_2066_);
if (v___x_2067_ == 0)
{
v_map_2026_ = v_fst_2065_;
v___y_2027_ = v_a_2019_;
v___y_2028_ = v_a_2020_;
v___y_2029_ = v_a_2021_;
v___y_2030_ = v_a_2022_;
v___y_2031_ = v_a_2023_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_box(2);
lean_inc(v_discr_2066_);
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2065_, v_discr_2066_, v___x_2068_);
v_map_2026_ = v___x_2069_;
v___y_2027_ = v_a_2019_;
v___y_2028_ = v_a_2020_;
v___y_2029_ = v_a_2021_;
v___y_2030_ = v_a_2022_;
v___y_2031_ = v_a_2023_;
goto v___jp_2025_;
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_cs_2018_);
v_a_2070_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2063_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2063_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
v___jp_2025_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_st_mk_ref(v_map_2026_);
v___x_2033_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_2018_, v___x_2032_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec_ref(v_cs_2018_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2033_, 0);
lean_dec(v_unused_2042_);
v___x_2035_ = v___x_2033_;
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___x_2033_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = lean_st_ref_get(v___x_2032_);
lean_dec(v___x_2032_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v___x_2032_);
v_a_2043_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2033_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2033_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2086_, lean_object* v_x_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2086_, v_x_2087_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2095_, v_x_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
return v_res_2103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_a_2104_, lean_object* v_x_2105_){
_start:
{
if (lean_obj_tag(v_x_2105_) == 0)
{
uint8_t v___x_2106_; 
v___x_2106_ = 0;
return v___x_2106_;
}
else
{
lean_object* v_key_2107_; lean_object* v_tail_2108_; uint8_t v___x_2109_; 
v_key_2107_ = lean_ctor_get(v_x_2105_, 0);
v_tail_2108_ = lean_ctor_get(v_x_2105_, 2);
v___x_2109_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2107_, v_a_2104_);
if (v___x_2109_ == 0)
{
v_x_2105_ = v_tail_2108_;
goto _start;
}
else
{
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_a_2111_, lean_object* v_x_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2111_, v_x_2112_);
lean_dec(v_x_2112_);
lean_dec(v_a_2111_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object* v_a_2115_, lean_object* v_b_2116_, lean_object* v_x_2117_){
_start:
{
if (lean_obj_tag(v_x_2117_) == 0)
{
lean_dec(v_b_2116_);
lean_dec(v_a_2115_);
return v_x_2117_;
}
else
{
lean_object* v_key_2118_; lean_object* v_value_2119_; lean_object* v_tail_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2132_; 
v_key_2118_ = lean_ctor_get(v_x_2117_, 0);
v_value_2119_ = lean_ctor_get(v_x_2117_, 1);
v_tail_2120_ = lean_ctor_get(v_x_2117_, 2);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2122_ = v_x_2117_;
v_isShared_2123_ = v_isSharedCheck_2132_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_tail_2120_);
lean_inc(v_value_2119_);
lean_inc(v_key_2118_);
lean_dec(v_x_2117_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2132_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint8_t v___x_2124_; 
v___x_2124_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2118_, v_a_2115_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2115_, v_b_2116_, v_tail_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 2, v___x_2125_);
v___x_2127_ = v___x_2122_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_key_2118_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_value_2119_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v___x_2130_; 
lean_dec(v_value_2119_);
lean_dec(v_key_2118_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_b_2116_);
lean_ctor_set(v___x_2122_, 0, v_a_2115_);
v___x_2130_ = v___x_2122_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2115_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_b_2116_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_tail_2120_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2134_) == 0)
{
return v_x_2133_;
}
else
{
lean_object* v_key_2135_; lean_object* v_value_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2160_; 
v_key_2135_ = lean_ctor_get(v_x_2134_, 0);
v_value_2136_ = lean_ctor_get(v_x_2134_, 1);
v_tail_2137_ = lean_ctor_get(v_x_2134_, 2);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2134_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2139_ = v_x_2134_;
v_isShared_2140_ = v_isSharedCheck_2160_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_value_2136_);
lean_inc(v_key_2135_);
lean_dec(v_x_2134_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2160_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; uint64_t v___x_2142_; uint64_t v___x_2143_; uint64_t v___x_2144_; uint64_t v_fold_2145_; uint64_t v___x_2146_; uint64_t v___x_2147_; uint64_t v___x_2148_; size_t v___x_2149_; size_t v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2141_ = lean_array_get_size(v_x_2133_);
v___x_2142_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_2135_);
v___x_2143_ = 32ULL;
v___x_2144_ = lean_uint64_shift_right(v___x_2142_, v___x_2143_);
v_fold_2145_ = lean_uint64_xor(v___x_2142_, v___x_2144_);
v___x_2146_ = 16ULL;
v___x_2147_ = lean_uint64_shift_right(v_fold_2145_, v___x_2146_);
v___x_2148_ = lean_uint64_xor(v_fold_2145_, v___x_2147_);
v___x_2149_ = lean_uint64_to_usize(v___x_2148_);
v___x_2150_ = lean_usize_of_nat(v___x_2141_);
v___x_2151_ = ((size_t)1ULL);
v___x_2152_ = lean_usize_sub(v___x_2150_, v___x_2151_);
v___x_2153_ = lean_usize_land(v___x_2149_, v___x_2152_);
v___x_2154_ = lean_array_uget_borrowed(v_x_2133_, v___x_2153_);
lean_inc(v___x_2154_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 2, v___x_2154_);
v___x_2156_ = v___x_2139_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_key_2135_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_value_2136_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_array_uset(v_x_2133_, v___x_2153_, v___x_2156_);
v_x_2133_ = v___x_2157_;
v_x_2134_ = v_tail_2137_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2161_, lean_object* v_source_2162_, lean_object* v_target_2163_){
_start:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_array_get_size(v_source_2162_);
v___x_2165_ = lean_nat_dec_lt(v_i_2161_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v_source_2162_);
lean_dec(v_i_2161_);
return v_target_2163_;
}
else
{
lean_object* v_es_2166_; lean_object* v___x_2167_; lean_object* v_source_2168_; lean_object* v_target_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_es_2166_ = lean_array_fget(v_source_2162_, v_i_2161_);
v___x_2167_ = lean_box(0);
v_source_2168_ = lean_array_fset(v_source_2162_, v_i_2161_, v___x_2167_);
v_target_2169_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2163_, v_es_2166_);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_add(v_i_2161_, v___x_2170_);
lean_dec(v_i_2161_);
v_i_2161_ = v___x_2171_;
v_source_2162_ = v_source_2168_;
v_target_2163_ = v_target_2169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object* v_data_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_nbuckets_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2174_ = lean_array_get_size(v_data_2173_);
v___x_2175_ = lean_unsigned_to_nat(2u);
v_nbuckets_2176_ = lean_nat_mul(v___x_2174_, v___x_2175_);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_mk_array(v_nbuckets_2176_, v___x_2178_);
v___x_2180_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2177_, v_data_2173_, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2181_, lean_object* v_a_2182_, lean_object* v_b_2183_){
_start:
{
lean_object* v_size_2184_; lean_object* v_buckets_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2228_; 
v_size_2184_ = lean_ctor_get(v_m_2181_, 0);
v_buckets_2185_ = lean_ctor_get(v_m_2181_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_m_2181_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2187_ = v_m_2181_;
v_isShared_2188_ = v_isSharedCheck_2228_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_buckets_2185_);
lean_inc(v_size_2184_);
lean_dec(v_m_2181_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2228_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; uint64_t v___x_2190_; uint64_t v___x_2191_; uint64_t v___x_2192_; uint64_t v_fold_2193_; uint64_t v___x_2194_; uint64_t v___x_2195_; uint64_t v___x_2196_; size_t v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v_bkt_2202_; uint8_t v___x_2203_; 
v___x_2189_ = lean_array_get_size(v_buckets_2185_);
v___x_2190_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2182_);
v___x_2191_ = 32ULL;
v___x_2192_ = lean_uint64_shift_right(v___x_2190_, v___x_2191_);
v_fold_2193_ = lean_uint64_xor(v___x_2190_, v___x_2192_);
v___x_2194_ = 16ULL;
v___x_2195_ = lean_uint64_shift_right(v_fold_2193_, v___x_2194_);
v___x_2196_ = lean_uint64_xor(v_fold_2193_, v___x_2195_);
v___x_2197_ = lean_uint64_to_usize(v___x_2196_);
v___x_2198_ = lean_usize_of_nat(v___x_2189_);
v___x_2199_ = ((size_t)1ULL);
v___x_2200_ = lean_usize_sub(v___x_2198_, v___x_2199_);
v___x_2201_ = lean_usize_land(v___x_2197_, v___x_2200_);
v_bkt_2202_ = lean_array_uget_borrowed(v_buckets_2185_, v___x_2201_);
v___x_2203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2182_, v_bkt_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v_size_x27_2205_; lean_object* v___x_2206_; lean_object* v_buckets_x27_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2204_ = lean_unsigned_to_nat(1u);
v_size_x27_2205_ = lean_nat_add(v_size_2184_, v___x_2204_);
lean_dec(v_size_2184_);
lean_inc(v_bkt_2202_);
v___x_2206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2182_);
lean_ctor_set(v___x_2206_, 1, v_b_2183_);
lean_ctor_set(v___x_2206_, 2, v_bkt_2202_);
v_buckets_x27_2207_ = lean_array_uset(v_buckets_2185_, v___x_2201_, v___x_2206_);
v___x_2208_ = lean_unsigned_to_nat(4u);
v___x_2209_ = lean_nat_mul(v_size_x27_2205_, v___x_2208_);
v___x_2210_ = lean_unsigned_to_nat(3u);
v___x_2211_ = lean_nat_div(v___x_2209_, v___x_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_array_get_size(v_buckets_x27_2207_);
v___x_2213_ = lean_nat_dec_le(v___x_2211_, v___x_2212_);
lean_dec(v___x_2211_);
if (v___x_2213_ == 0)
{
lean_object* v_val_2214_; lean_object* v___x_2216_; 
v_val_2214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2207_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v_val_2214_);
lean_ctor_set(v___x_2187_, 0, v_size_x27_2205_);
v___x_2216_ = v___x_2187_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_size_x27_2205_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_val_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
else
{
lean_object* v___x_2219_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v_buckets_x27_2207_);
lean_ctor_set(v___x_2187_, 0, v_size_x27_2205_);
v___x_2219_ = v___x_2187_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_size_x27_2205_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_buckets_x27_2207_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v_buckets_x27_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_inc(v_bkt_2202_);
v___x_2221_ = lean_box(0);
v_buckets_x27_2222_ = lean_array_uset(v_buckets_2185_, v___x_2201_, v___x_2221_);
v___x_2223_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2182_, v_b_2183_, v_bkt_2202_);
v___x_2224_ = lean_array_uset(v_buckets_x27_2222_, v___x_2201_, v___x_2223_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v___x_2224_);
v___x_2226_ = v___x_2187_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_size_2184_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2224_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2229_, size_t v_i_2230_, size_t v_stop_2231_, lean_object* v_b_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_usize_dec_eq(v_i_2230_, v_stop_2231_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2234_ = lean_box(0);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_sub(v_i_2230_, v___x_2235_);
v___x_2237_ = lean_array_uget_borrowed(v_as_2229_, v___x_2236_);
v___x_2238_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2237_);
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2232_, v___x_2238_, v___x_2234_);
v_i_2230_ = v___x_2236_;
v_b_2232_ = v___x_2239_;
goto _start;
}
else
{
return v_b_2232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2241_, lean_object* v_i_2242_, lean_object* v_stop_2243_, lean_object* v_b_2244_){
_start:
{
size_t v_i_boxed_2245_; size_t v_stop_boxed_2246_; lean_object* v_res_2247_; 
v_i_boxed_2245_ = lean_unbox_usize(v_i_2242_);
lean_dec(v_i_2242_);
v_stop_boxed_2246_ = lean_unbox_usize(v_stop_2243_);
lean_dec(v_stop_2243_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2241_, v_i_boxed_2245_, v_stop_boxed_2246_, v_b_2244_);
lean_dec_ref(v_as_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2248_){
_start:
{
lean_object* v_alts_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_map_2264_; uint8_t v___x_2265_; 
v_alts_2249_ = lean_ctor_get(v_cs_2248_, 3);
v___x_2250_ = lean_array_get_size(v_alts_2249_);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_add(v___x_2250_, v___x_2251_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = lean_unsigned_to_nat(4u);
v___x_2255_ = lean_nat_mul(v___x_2252_, v___x_2254_);
lean_dec(v___x_2252_);
v___x_2256_ = lean_unsigned_to_nat(3u);
v___x_2257_ = lean_nat_div(v___x_2255_, v___x_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = l_Nat_nextPowerOfTwo(v___x_2257_);
lean_dec(v___x_2257_);
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_mk_array(v___x_2258_, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2253_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_box(2);
v___x_2263_ = lean_box(0);
v_map_2264_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2261_, v___x_2262_, v___x_2263_);
v___x_2265_ = lean_nat_dec_lt(v___x_2253_, v___x_2250_);
if (v___x_2265_ == 0)
{
return v_map_2264_;
}
else
{
size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_usize_of_nat(v___x_2250_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2249_, v___x_2266_, v___x_2267_, v_map_2264_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2269_);
lean_dec_ref(v_cs_2269_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2271_, lean_object* v_m_2272_, lean_object* v_a_2273_, lean_object* v_b_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2272_, v_a_2273_, v_b_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2276_, lean_object* v_a_2277_, lean_object* v_x_2278_){
_start:
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2277_, v_x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2280_, lean_object* v_a_2281_, lean_object* v_x_2282_){
_start:
{
uint8_t v_res_2283_; lean_object* v_r_2284_; 
v_res_2283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2280_, v_a_2281_, v_x_2282_);
lean_dec(v_x_2282_);
lean_dec(v_a_2281_);
v_r_2284_ = lean_box(v_res_2283_);
return v_r_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2285_, lean_object* v_data_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2288_, lean_object* v_a_2289_, lean_object* v_b_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2289_, v_b_2290_, v_x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2293_, lean_object* v_i_2294_, lean_object* v_source_2295_, lean_object* v_target_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2294_, v_source_2295_, v_target_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2298_, lean_object* v_x_2299_, lean_object* v_x_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2299_, v_x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; lean_object* v_decision_2306_; uint8_t v___x_2307_; 
v___x_2305_ = lean_st_ref_get(v_a_2303_);
v_decision_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc_ref(v_decision_2306_);
lean_dec(v___x_2305_);
v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2306_, v_fvar_2302_);
lean_dec_ref(v_decision_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_dec(v_fvar_2302_);
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; lean_object* v_decision_2311_; lean_object* v_newArms_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2324_; 
v___x_2310_ = lean_st_ref_take(v_a_2303_);
v_decision_2311_ = lean_ctor_get(v___x_2310_, 0);
v_newArms_2312_ = lean_ctor_get(v___x_2310_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2314_ = v___x_2310_;
v_isShared_2315_ = v_isSharedCheck_2324_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_newArms_2312_);
lean_inc(v_decision_2311_);
lean_dec(v___x_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2324_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2316_ = lean_box(2);
v___x_2317_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2311_, v_fvar_2302_, v___x_2316_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2317_);
v___x_2319_ = v___x_2314_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_newArms_2312_);
v___x_2319_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_st_ref_set(v_a_2303_, v___x_2319_);
v___x_2321_ = lean_box(0);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2325_, v_a_2326_);
lean_dec(v_a_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2329_, v_a_2330_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec(v_a_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v_toApplicative_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2420_; 
v___x_2355_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2356_ = l_StateRefT_x27_instMonad___redArg(v___x_2355_);
v_toApplicative_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2356_, 1);
lean_dec(v_unused_2421_);
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2420_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_toApplicative_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2420_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v_toFunctor_2361_; lean_object* v_toSeq_2362_; lean_object* v_toSeqLeft_2363_; lean_object* v_toSeqRight_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2418_; 
v_toFunctor_2361_ = lean_ctor_get(v_toApplicative_2357_, 0);
v_toSeq_2362_ = lean_ctor_get(v_toApplicative_2357_, 2);
v_toSeqLeft_2363_ = lean_ctor_get(v_toApplicative_2357_, 3);
v_toSeqRight_2364_ = lean_ctor_get(v_toApplicative_2357_, 4);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_toApplicative_2357_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v_toApplicative_2357_, 1);
lean_dec(v_unused_2419_);
v___x_2366_ = v_toApplicative_2357_;
v_isShared_2367_ = v_isSharedCheck_2418_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_toSeqRight_2364_);
lean_inc(v_toSeqLeft_2363_);
lean_inc(v_toSeq_2362_);
lean_inc(v_toFunctor_2361_);
lean_dec(v_toApplicative_2357_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2418_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___f_2368_; lean_object* v___f_2369_; lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___x_2377_; 
v___f_2368_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2369_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2361_);
v___f_2370_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2370_, 0, v_toFunctor_2361_);
v___f_2371_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2371_, 0, v_toFunctor_2361_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___f_2370_);
lean_ctor_set(v___x_2372_, 1, v___f_2371_);
v___f_2373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2373_, 0, v_toSeqRight_2364_);
v___f_2374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2374_, 0, v_toSeqLeft_2363_);
v___f_2375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2375_, 0, v_toSeq_2362_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 4, v___f_2373_);
lean_ctor_set(v___x_2366_, 3, v___f_2374_);
lean_ctor_set(v___x_2366_, 2, v___f_2375_);
lean_ctor_set(v___x_2366_, 1, v___f_2368_);
lean_ctor_set(v___x_2366_, 0, v___x_2372_);
v___x_2377_ = v___x_2366_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___f_2368_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v___f_2375_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v___f_2374_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v___f_2373_);
v___x_2377_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___f_2369_);
lean_ctor_set(v___x_2359_, 0, v___x_2377_);
v___x_2379_ = v___x_2359_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___f_2369_);
v___x_2379_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v_toApplicative_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2414_; 
v___x_2380_ = l_StateRefT_x27_instMonad___redArg(v___x_2379_);
v_toApplicative_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v___x_2380_, 1);
lean_dec(v_unused_2415_);
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2414_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_toApplicative_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2414_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_toFunctor_2385_; lean_object* v_toSeq_2386_; lean_object* v_toSeqLeft_2387_; lean_object* v_toSeqRight_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2412_; 
v_toFunctor_2385_ = lean_ctor_get(v_toApplicative_2381_, 0);
v_toSeq_2386_ = lean_ctor_get(v_toApplicative_2381_, 2);
v_toSeqLeft_2387_ = lean_ctor_get(v_toApplicative_2381_, 3);
v_toSeqRight_2388_ = lean_ctor_get(v_toApplicative_2381_, 4);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_toApplicative_2381_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; 
v_unused_2413_ = lean_ctor_get(v_toApplicative_2381_, 1);
lean_dec(v_unused_2413_);
v___x_2390_ = v_toApplicative_2381_;
v_isShared_2391_ = v_isSharedCheck_2412_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_toSeqRight_2388_);
lean_inc(v_toSeqLeft_2387_);
lean_inc(v_toSeq_2386_);
lean_inc(v_toFunctor_2385_);
lean_dec(v_toApplicative_2381_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2412_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___f_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___f_2399_; lean_object* v___x_2401_; 
v___f_2392_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2393_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2385_);
v___f_2394_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2394_, 0, v_toFunctor_2385_);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2395_, 0, v_toFunctor_2385_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___f_2394_);
lean_ctor_set(v___x_2396_, 1, v___f_2395_);
v___f_2397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2397_, 0, v_toSeqRight_2388_);
v___f_2398_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2398_, 0, v_toSeqLeft_2387_);
v___f_2399_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2399_, 0, v_toSeq_2386_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v___f_2397_);
lean_ctor_set(v___x_2390_, 3, v___f_2398_);
lean_ctor_set(v___x_2390_, 2, v___f_2399_);
lean_ctor_set(v___x_2390_, 1, v___f_2392_);
lean_ctor_set(v___x_2390_, 0, v___x_2396_);
v___x_2401_ = v___x_2390_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___f_2392_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v___f_2399_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v___f_2398_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v___f_2397_);
v___x_2401_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v___f_2393_);
lean_ctor_set(v___x_2383_, 0, v___x_2401_);
v___x_2403_ = v___x_2383_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___f_2393_);
v___x_2403_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_12636__overap_2408_; lean_object* v___x_2409_; 
v___x_2404_ = l_ReaderT_instMonad___redArg(v___x_2403_);
v___x_2405_ = l_StateRefT_x27_instMonad___redArg(v___x_2404_);
v___x_2406_ = lean_box(0);
v___x_2407_ = l_instInhabitedOfMonad___redArg(v___x_2405_, v___x_2406_);
v___x_12636__overap_2408_ = lean_panic_fn_borrowed(v___x_2407_, v_msg_2347_);
lean_dec(v___x_2407_);
lean_inc(v___y_2353_);
lean_inc_ref(v___y_2352_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc(v___y_2348_);
v___x_2409_ = lean_apply_7(v___x_12636__overap_2408_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, lean_box(0));
return v___x_2409_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec(v___y_2423_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2431_, lean_object* v_e_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_ty_2441_; lean_object* v_body_2442_; uint8_t v___x_2445_; 
v___x_2445_ = l_Lean_Expr_hasFVar(v_e_2432_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec_ref(v_e_2432_);
lean_dec_ref(v_f_2431_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
else
{
switch(lean_obj_tag(v_e_2432_))
{
case 1:
{
lean_object* v_fvarId_2448_; lean_object* v___x_2449_; 
v_fvarId_2448_ = lean_ctor_get(v_e_2432_, 0);
lean_inc(v_fvarId_2448_);
lean_dec_ref_known(v_e_2432_, 1);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2434_);
lean_inc(v___y_2433_);
v___x_2449_ = lean_apply_8(v_f_2431_, v_fvarId_2448_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, lean_box(0));
return v___x_2449_;
}
case 2:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec_ref_known(v_e_2432_, 1);
lean_dec_ref(v_f_2431_);
v___x_2450_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2451_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2450_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2451_;
}
case 5:
{
lean_object* v_fn_2452_; lean_object* v_arg_2453_; lean_object* v___x_2454_; 
v_fn_2452_ = lean_ctor_get(v_e_2432_, 0);
lean_inc_ref(v_fn_2452_);
v_arg_2453_ = lean_ctor_get(v_e_2432_, 1);
lean_inc_ref(v_arg_2453_);
lean_dec_ref_known(v_e_2432_, 2);
lean_inc_ref(v_f_2431_);
v___x_2454_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2431_, v_fn_2452_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_dec_ref_known(v___x_2454_, 1);
v_e_2432_ = v_arg_2453_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2453_);
lean_dec_ref(v_f_2431_);
return v___x_2454_;
}
}
case 6:
{
lean_object* v_binderType_2456_; lean_object* v_body_2457_; 
v_binderType_2456_ = lean_ctor_get(v_e_2432_, 1);
lean_inc_ref(v_binderType_2456_);
v_body_2457_ = lean_ctor_get(v_e_2432_, 2);
lean_inc_ref(v_body_2457_);
lean_dec_ref_known(v_e_2432_, 3);
v_ty_2441_ = v_binderType_2456_;
v_body_2442_ = v_body_2457_;
goto v___jp_2440_;
}
case 7:
{
lean_object* v_binderType_2458_; lean_object* v_body_2459_; 
v_binderType_2458_ = lean_ctor_get(v_e_2432_, 1);
lean_inc_ref(v_binderType_2458_);
v_body_2459_ = lean_ctor_get(v_e_2432_, 2);
lean_inc_ref(v_body_2459_);
lean_dec_ref_known(v_e_2432_, 3);
v_ty_2441_ = v_binderType_2458_;
v_body_2442_ = v_body_2459_;
goto v___jp_2440_;
}
case 8:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_dec_ref_known(v_e_2432_, 4);
lean_dec_ref(v_f_2431_);
v___x_2460_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2461_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2460_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2461_;
}
case 11:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec_ref_known(v_e_2432_, 3);
lean_dec_ref(v_f_2431_);
v___x_2462_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2463_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2462_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2463_;
}
default: 
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_dec_ref(v_e_2432_);
lean_dec_ref(v_f_2431_);
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
}
v___jp_2440_:
{
lean_object* v___x_2443_; 
lean_inc_ref(v_f_2431_);
v___x_2443_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2431_, v_ty_2441_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_dec_ref_known(v___x_2443_, 1);
v_e_2432_ = v_body_2442_;
goto _start;
}
else
{
lean_dec_ref(v_body_2442_);
lean_dec_ref(v_f_2431_);
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2466_, lean_object* v_e_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2466_, v_e_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2476_, lean_object* v_arg_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
switch(lean_obj_tag(v_arg_2477_))
{
case 0:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v_f_2476_);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
return v___x_2486_;
}
case 1:
{
lean_object* v_fvarId_2487_; lean_object* v___x_2488_; 
v_fvarId_2487_ = lean_ctor_get(v_arg_2477_, 0);
lean_inc(v_fvarId_2487_);
lean_dec_ref_known(v_arg_2477_, 1);
lean_inc(v___y_2483_);
lean_inc_ref(v___y_2482_);
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc(v___y_2478_);
v___x_2488_ = lean_apply_8(v_f_2476_, v_fvarId_2487_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, lean_box(0));
return v___x_2488_;
}
default: 
{
lean_object* v_expr_2489_; lean_object* v___x_2490_; 
v_expr_2489_ = lean_ctor_get(v_arg_2477_, 0);
lean_inc_ref(v_expr_2489_);
lean_dec_ref_known(v_arg_2477_, 1);
v___x_2490_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2476_, v_expr_2489_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2491_, lean_object* v_arg_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2491_, v_arg_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2501_, lean_object* v_param_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_type_2510_; lean_object* v___x_2511_; 
v_type_2510_ = lean_ctor_get(v_param_2502_, 2);
lean_inc_ref(v_type_2510_);
lean_dec_ref(v_param_2502_);
v___x_2511_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2501_, v_type_2510_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2512_, lean_object* v_param_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2512_, v_param_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2522_, lean_object* v_f_2523_, lean_object* v_as_2524_, size_t v_i_2525_, size_t v_stop_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_usize_dec_eq(v_i_2525_, v_stop_2526_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_array_uget_borrowed(v_as_2524_, v_i_2525_);
lean_inc(v___x_2536_);
lean_inc_ref(v_f_2523_);
v___x_2537_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2523_, v___x_2536_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; size_t v___x_2539_; size_t v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_add(v_i_2525_, v___x_2539_);
v_i_2525_ = v___x_2540_;
v_b_2527_ = v_a_2538_;
goto _start;
}
else
{
lean_dec_ref(v_f_2523_);
return v___x_2537_;
}
}
else
{
lean_object* v___x_2542_; 
lean_dec_ref(v_f_2523_);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_b_2527_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2543_, lean_object* v_f_2544_, lean_object* v_as_2545_, lean_object* v_i_2546_, lean_object* v_stop_2547_, lean_object* v_b_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
uint8_t v_pu_boxed_2556_; size_t v_i_boxed_2557_; size_t v_stop_boxed_2558_; lean_object* v_res_2559_; 
v_pu_boxed_2556_ = lean_unbox(v_pu_2543_);
v_i_boxed_2557_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_stop_boxed_2558_ = lean_unbox_usize(v_stop_2547_);
lean_dec(v_stop_2547_);
v_res_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2556_, v_f_2544_, v_as_2545_, v_i_boxed_2557_, v_stop_boxed_2558_, v_b_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v_as_2545_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2560_, lean_object* v_f_2561_, lean_object* v_as_2562_, size_t v_i_2563_, size_t v_stop_2564_, lean_object* v_b_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_usize_dec_eq(v_i_2563_, v_stop_2564_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_array_uget_borrowed(v_as_2562_, v_i_2563_);
lean_inc(v___x_2574_);
lean_inc_ref(v_f_2561_);
v___x_2575_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2561_, v___x_2574_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; size_t v___x_2577_; size_t v___x_2578_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_add(v_i_2563_, v___x_2577_);
v_i_2563_ = v___x_2578_;
v_b_2565_ = v_a_2576_;
goto _start;
}
else
{
lean_dec_ref(v_f_2561_);
return v___x_2575_;
}
}
else
{
lean_object* v___x_2580_; 
lean_dec_ref(v_f_2561_);
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_b_2565_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2581_, lean_object* v_f_2582_, lean_object* v_as_2583_, lean_object* v_i_2584_, lean_object* v_stop_2585_, lean_object* v_b_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
uint8_t v_pu_boxed_2594_; size_t v_i_boxed_2595_; size_t v_stop_boxed_2596_; lean_object* v_res_2597_; 
v_pu_boxed_2594_ = lean_unbox(v_pu_2581_);
v_i_boxed_2595_ = lean_unbox_usize(v_i_2584_);
lean_dec(v_i_2584_);
v_stop_boxed_2596_ = lean_unbox_usize(v_stop_2585_);
lean_dec(v_stop_2585_);
v_res_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2594_, v_f_2582_, v_as_2583_, v_i_boxed_2595_, v_stop_boxed_2596_, v_b_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v_as_2583_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2598_, lean_object* v_f_2599_, lean_object* v_e_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_args_2609_; 
switch(lean_obj_tag(v_e_2600_))
{
case 2:
{
lean_object* v_struct_2623_; lean_object* v___x_2624_; 
v_struct_2623_ = lean_ctor_get(v_e_2600_, 2);
lean_inc(v_struct_2623_);
lean_dec_ref_known(v_e_2600_, 3);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2624_ = lean_apply_8(v_f_2599_, v_struct_2623_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2624_;
}
case 3:
{
lean_object* v_args_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_args_2625_ = lean_ctor_get(v_e_2600_, 2);
lean_inc_ref(v_args_2625_);
lean_dec_ref_known(v_e_2600_, 3);
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = lean_array_get_size(v_args_2625_);
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_nat_dec_lt(v___x_2626_, v___x_2627_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v_args_2625_);
lean_dec_ref(v_f_2599_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
return v___x_2630_;
}
else
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_nat_dec_le(v___x_2627_, v___x_2627_);
if (v___x_2631_ == 0)
{
if (v___x_2629_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_args_2625_);
lean_dec_ref(v_f_2599_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2628_);
return v___x_2632_;
}
else
{
size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = lean_usize_of_nat(v___x_2627_);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2625_, v___x_2633_, v___x_2634_, v___x_2628_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2625_);
return v___x_2635_;
}
}
else
{
size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = ((size_t)0ULL);
v___x_2637_ = lean_usize_of_nat(v___x_2627_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2625_, v___x_2636_, v___x_2637_, v___x_2628_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2625_);
return v___x_2638_;
}
}
}
case 4:
{
lean_object* v_fvarId_2639_; lean_object* v_args_2640_; lean_object* v___x_2641_; 
v_fvarId_2639_ = lean_ctor_get(v_e_2600_, 0);
lean_inc(v_fvarId_2639_);
v_args_2640_ = lean_ctor_get(v_e_2600_, 1);
lean_inc_ref(v_args_2640_);
lean_dec_ref_known(v_e_2600_, 2);
lean_inc_ref(v_f_2599_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2641_ = lean_apply_8(v_f_2599_, v_fvarId_2639_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2662_; 
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v___x_2641_, 0);
lean_dec(v_unused_2663_);
v___x_2643_ = v___x_2641_;
v_isShared_2644_ = v_isSharedCheck_2662_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v___x_2641_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2662_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = lean_array_get_size(v_args_2640_);
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_nat_dec_lt(v___x_2645_, v___x_2646_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref(v_args_2640_);
lean_dec_ref(v_f_2599_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2647_);
v___x_2650_ = v___x_2643_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2647_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_nat_dec_le(v___x_2646_, v___x_2646_);
if (v___x_2652_ == 0)
{
if (v___x_2648_ == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref(v_args_2640_);
lean_dec_ref(v_f_2599_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2647_);
v___x_2654_ = v___x_2643_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2647_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2643_);
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2646_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2640_, v___x_2656_, v___x_2657_, v___x_2647_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2640_);
return v___x_2658_;
}
}
else
{
size_t v___x_2659_; size_t v___x_2660_; lean_object* v___x_2661_; 
lean_del_object(v___x_2643_);
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = lean_usize_of_nat(v___x_2646_);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2640_, v___x_2659_, v___x_2660_, v___x_2647_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2640_);
return v___x_2661_;
}
}
}
}
else
{
lean_dec_ref(v_args_2640_);
lean_dec_ref(v_f_2599_);
return v___x_2641_;
}
}
case 5:
{
lean_object* v_args_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_args_2664_ = lean_ctor_get(v_e_2600_, 1);
lean_inc_ref(v_args_2664_);
lean_dec_ref_known(v_e_2600_, 2);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v_args_2664_);
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref(v_args_2664_);
lean_dec_ref(v_f_2599_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
return v___x_2669_;
}
else
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2670_ == 0)
{
if (v___x_2668_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v_args_2664_);
lean_dec_ref(v_f_2599_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2667_);
return v___x_2671_;
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2666_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2664_, v___x_2672_, v___x_2673_, v___x_2667_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2664_);
return v___x_2674_;
}
}
else
{
size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((size_t)0ULL);
v___x_2676_ = lean_usize_of_nat(v___x_2666_);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2664_, v___x_2675_, v___x_2676_, v___x_2667_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2664_);
return v___x_2677_;
}
}
}
case 6:
{
lean_object* v_var_2678_; lean_object* v___x_2679_; 
v_var_2678_ = lean_ctor_get(v_e_2600_, 1);
lean_inc(v_var_2678_);
lean_dec_ref_known(v_e_2600_, 2);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2679_ = lean_apply_8(v_f_2599_, v_var_2678_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2679_;
}
case 7:
{
lean_object* v_var_2680_; lean_object* v___x_2681_; 
v_var_2680_ = lean_ctor_get(v_e_2600_, 1);
lean_inc(v_var_2680_);
lean_dec_ref_known(v_e_2600_, 2);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2681_ = lean_apply_8(v_f_2599_, v_var_2680_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2681_;
}
case 8:
{
lean_object* v_var_2682_; lean_object* v___x_2683_; 
v_var_2682_ = lean_ctor_get(v_e_2600_, 2);
lean_inc(v_var_2682_);
lean_dec_ref_known(v_e_2600_, 3);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2683_ = lean_apply_8(v_f_2599_, v_var_2682_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2683_;
}
case 9:
{
lean_object* v_args_2684_; 
v_args_2684_ = lean_ctor_get(v_e_2600_, 1);
lean_inc_ref(v_args_2684_);
lean_dec_ref_known(v_e_2600_, 2);
v_args_2609_ = v_args_2684_;
goto v___jp_2608_;
}
case 10:
{
lean_object* v_args_2685_; 
v_args_2685_ = lean_ctor_get(v_e_2600_, 1);
lean_inc_ref(v_args_2685_);
lean_dec_ref_known(v_e_2600_, 2);
v_args_2609_ = v_args_2685_;
goto v___jp_2608_;
}
case 11:
{
lean_object* v_var_2686_; lean_object* v___x_2687_; 
v_var_2686_ = lean_ctor_get(v_e_2600_, 1);
lean_inc(v_var_2686_);
lean_dec_ref_known(v_e_2600_, 2);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2687_ = lean_apply_8(v_f_2599_, v_var_2686_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2687_;
}
case 12:
{
lean_object* v_var_2688_; lean_object* v_args_2689_; lean_object* v___x_2690_; 
v_var_2688_ = lean_ctor_get(v_e_2600_, 0);
lean_inc(v_var_2688_);
v_args_2689_ = lean_ctor_get(v_e_2600_, 2);
lean_inc_ref(v_args_2689_);
lean_dec_ref_known(v_e_2600_, 3);
lean_inc_ref(v_f_2599_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2690_ = lean_apply_8(v_f_2599_, v_var_2688_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2711_; 
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; 
v_unused_2712_ = lean_ctor_get(v___x_2690_, 0);
lean_dec(v_unused_2712_);
v___x_2692_ = v___x_2690_;
v_isShared_2693_ = v_isSharedCheck_2711_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v___x_2690_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2711_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_array_get_size(v_args_2689_);
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_nat_dec_lt(v___x_2694_, v___x_2695_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2699_; 
lean_dec_ref(v_args_2689_);
lean_dec_ref(v_f_2599_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2696_);
v___x_2699_ = v___x_2692_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
else
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_nat_dec_le(v___x_2695_, v___x_2695_);
if (v___x_2701_ == 0)
{
if (v___x_2697_ == 0)
{
lean_object* v___x_2703_; 
lean_dec_ref(v_args_2689_);
lean_dec_ref(v_f_2599_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2696_);
v___x_2703_ = v___x_2692_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2696_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
else
{
size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
lean_del_object(v___x_2692_);
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = lean_usize_of_nat(v___x_2695_);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2689_, v___x_2705_, v___x_2706_, v___x_2696_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2689_);
return v___x_2707_;
}
}
else
{
size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
lean_del_object(v___x_2692_);
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = lean_usize_of_nat(v___x_2695_);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2689_, v___x_2708_, v___x_2709_, v___x_2696_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2689_);
return v___x_2710_;
}
}
}
}
else
{
lean_dec_ref(v_args_2689_);
lean_dec_ref(v_f_2599_);
return v___x_2690_;
}
}
case 13:
{
lean_object* v_fvarId_2713_; lean_object* v___x_2714_; 
v_fvarId_2713_ = lean_ctor_get(v_e_2600_, 1);
lean_inc(v_fvarId_2713_);
lean_dec_ref_known(v_e_2600_, 2);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2714_ = lean_apply_8(v_f_2599_, v_fvarId_2713_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2714_;
}
case 14:
{
lean_object* v_fvarId_2715_; lean_object* v___x_2716_; 
v_fvarId_2715_ = lean_ctor_get(v_e_2600_, 0);
lean_inc(v_fvarId_2715_);
lean_dec_ref_known(v_e_2600_, 1);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2716_ = lean_apply_8(v_f_2599_, v_fvarId_2715_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2716_;
}
case 15:
{
lean_object* v_fvarId_2717_; lean_object* v___x_2718_; 
v_fvarId_2717_ = lean_ctor_get(v_e_2600_, 0);
lean_inc(v_fvarId_2717_);
lean_dec_ref_known(v_e_2600_, 1);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
v___x_2718_ = lean_apply_8(v_f_2599_, v_fvarId_2717_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2718_;
}
default: 
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec(v_e_2600_);
lean_dec_ref(v_f_2599_);
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
}
v___jp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_array_get_size(v_args_2609_);
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref(v_args_2609_);
lean_dec_ref(v_f_2599_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
return v___x_2614_;
}
else
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_nat_dec_le(v___x_2611_, v___x_2611_);
if (v___x_2615_ == 0)
{
if (v___x_2613_ == 0)
{
lean_object* v___x_2616_; 
lean_dec_ref(v_args_2609_);
lean_dec_ref(v_f_2599_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2612_);
return v___x_2616_;
}
else
{
size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = ((size_t)0ULL);
v___x_2618_ = lean_usize_of_nat(v___x_2611_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2609_, v___x_2617_, v___x_2618_, v___x_2612_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2609_);
return v___x_2619_;
}
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = lean_usize_of_nat(v___x_2611_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2598_, v_f_2599_, v_args_2609_, v___x_2620_, v___x_2621_, v___x_2612_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_args_2609_);
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2721_, lean_object* v_f_2722_, lean_object* v_e_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v_pu_boxed_2731_; lean_object* v_res_2732_; 
v_pu_boxed_2731_ = lean_unbox(v_pu_2721_);
v_res_2732_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2731_, v_f_2722_, v_e_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2724_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2733_, lean_object* v_f_2734_, lean_object* v_decl_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_type_2743_; lean_object* v_value_2744_; lean_object* v___x_2745_; 
v_type_2743_ = lean_ctor_get(v_decl_2735_, 2);
lean_inc_ref(v_type_2743_);
v_value_2744_ = lean_ctor_get(v_decl_2735_, 3);
lean_inc(v_value_2744_);
lean_dec_ref(v_decl_2735_);
lean_inc_ref(v_f_2734_);
v___x_2745_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2734_, v_type_2743_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v___x_2746_; 
lean_dec_ref_known(v___x_2745_, 1);
v___x_2746_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2733_, v_f_2734_, v_value_2744_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2746_;
}
else
{
lean_dec(v_value_2744_);
lean_dec_ref(v_f_2734_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2747_, lean_object* v_f_2748_, lean_object* v_decl_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v_pu_boxed_2757_; lean_object* v_res_2758_; 
v_pu_boxed_2757_ = lean_unbox(v_pu_2747_);
v_res_2758_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2757_, v_f_2748_, v_decl_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2759_, lean_object* v_f_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
switch(lean_obj_tag(v_alt_2759_))
{
case 0:
{
lean_object* v_code_2768_; lean_object* v___x_2769_; 
v_code_2768_ = lean_ctor_get(v_alt_2759_, 2);
lean_inc_ref(v_code_2768_);
lean_dec_ref_known(v_alt_2759_, 3);
lean_inc(v___y_2766_);
lean_inc_ref(v___y_2765_);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc(v___y_2761_);
v___x_2769_ = lean_apply_8(v_f_2760_, v_code_2768_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, lean_box(0));
return v___x_2769_;
}
case 1:
{
lean_object* v_code_2770_; lean_object* v___x_2771_; 
v_code_2770_ = lean_ctor_get(v_alt_2759_, 1);
lean_inc_ref(v_code_2770_);
lean_dec_ref_known(v_alt_2759_, 2);
lean_inc(v___y_2766_);
lean_inc_ref(v___y_2765_);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc(v___y_2761_);
v___x_2771_ = lean_apply_8(v_f_2760_, v_code_2770_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, lean_box(0));
return v___x_2771_;
}
default: 
{
lean_object* v_code_2772_; lean_object* v___x_2773_; 
v_code_2772_ = lean_ctor_get(v_alt_2759_, 0);
lean_inc_ref(v_code_2772_);
lean_dec_ref_known(v_alt_2759_, 1);
lean_inc(v___y_2766_);
lean_inc_ref(v___y_2765_);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc(v___y_2761_);
v___x_2773_ = lean_apply_8(v_f_2760_, v_code_2772_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, lean_box(0));
return v___x_2773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2774_, lean_object* v_f_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2774_, v_f_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2776_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2784_, lean_object* v_f_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
uint8_t v_pu_boxed_2794_; lean_object* v_res_2795_; 
v_pu_boxed_2794_ = lean_unbox(v_pu_2784_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2794_, v_f_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec(v___y_2787_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2796_, lean_object* v_f_2797_, lean_object* v_as_2798_, size_t v_i_2799_, size_t v_stop_2800_, lean_object* v_b_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_usize_dec_eq(v_i_2799_, v_stop_2800_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2810_ = lean_box(v_pu_2796_);
lean_inc_ref(v_f_2797_);
v___f_2811_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2811_, 0, v___x_2810_);
lean_closure_set(v___f_2811_, 1, v_f_2797_);
v___x_2812_ = lean_array_uget_borrowed(v_as_2798_, v_i_2799_);
lean_inc(v___x_2812_);
v___x_2813_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2812_, v___f_2811_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; size_t v___x_2815_; size_t v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = ((size_t)1ULL);
v___x_2816_ = lean_usize_add(v_i_2799_, v___x_2815_);
v_i_2799_ = v___x_2816_;
v_b_2801_ = v_a_2814_;
goto _start;
}
else
{
lean_dec_ref(v_f_2797_);
return v___x_2813_;
}
}
else
{
lean_object* v___x_2818_; 
lean_dec_ref(v_f_2797_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_b_2801_);
return v___x_2818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2819_, lean_object* v_f_2820_, lean_object* v_c_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
switch(lean_obj_tag(v_c_2821_))
{
case 0:
{
lean_object* v_decl_2829_; lean_object* v_k_2830_; lean_object* v___x_2831_; 
v_decl_2829_ = lean_ctor_get(v_c_2821_, 0);
lean_inc_ref(v_decl_2829_);
v_k_2830_ = lean_ctor_get(v_c_2821_, 1);
lean_inc_ref(v_k_2830_);
lean_dec_ref_known(v_c_2821_, 2);
lean_inc_ref(v_f_2820_);
v___x_2831_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2819_, v_f_2820_, v_decl_2829_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
v_c_2821_ = v_k_2830_;
goto _start;
}
else
{
lean_dec_ref(v_k_2830_);
lean_dec_ref(v_f_2820_);
return v___x_2831_;
}
}
case 3:
{
lean_object* v_fvarId_2833_; lean_object* v_args_2834_; lean_object* v___x_2835_; 
v_fvarId_2833_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2833_);
v_args_2834_ = lean_ctor_get(v_c_2821_, 1);
lean_inc_ref(v_args_2834_);
lean_dec_ref_known(v_c_2821_, 2);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2835_ = lean_apply_8(v_f_2820_, v_fvarId_2833_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2856_; 
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2835_, 0);
lean_dec(v_unused_2857_);
v___x_2837_ = v___x_2835_;
v_isShared_2838_ = v_isSharedCheck_2856_;
goto v_resetjp_2836_;
}
else
{
lean_dec(v___x_2835_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2856_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = lean_array_get_size(v_args_2834_);
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_nat_dec_lt(v___x_2839_, v___x_2840_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2844_; 
lean_dec_ref(v_args_2834_);
lean_dec_ref(v_f_2820_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2841_);
v___x_2844_ = v___x_2837_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2841_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
else
{
uint8_t v___x_2846_; 
v___x_2846_ = lean_nat_dec_le(v___x_2840_, v___x_2840_);
if (v___x_2846_ == 0)
{
if (v___x_2842_ == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref(v_args_2834_);
lean_dec_ref(v_f_2820_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2841_);
v___x_2848_ = v___x_2837_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2841_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
else
{
size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
lean_del_object(v___x_2837_);
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = lean_usize_of_nat(v___x_2840_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2819_, v_f_2820_, v_args_2834_, v___x_2850_, v___x_2851_, v___x_2841_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec_ref(v_args_2834_);
return v___x_2852_;
}
}
else
{
size_t v___x_2853_; size_t v___x_2854_; lean_object* v___x_2855_; 
lean_del_object(v___x_2837_);
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = lean_usize_of_nat(v___x_2840_);
v___x_2855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2819_, v_f_2820_, v_args_2834_, v___x_2853_, v___x_2854_, v___x_2841_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec_ref(v_args_2834_);
return v___x_2855_;
}
}
}
}
else
{
lean_dec_ref(v_args_2834_);
lean_dec_ref(v_f_2820_);
return v___x_2835_;
}
}
case 4:
{
lean_object* v_cases_2858_; lean_object* v_resultType_2859_; lean_object* v_discr_2860_; lean_object* v_alts_2861_; lean_object* v___x_2862_; 
v_cases_2858_ = lean_ctor_get(v_c_2821_, 0);
lean_inc_ref(v_cases_2858_);
lean_dec_ref_known(v_c_2821_, 1);
v_resultType_2859_ = lean_ctor_get(v_cases_2858_, 1);
lean_inc_ref(v_resultType_2859_);
v_discr_2860_ = lean_ctor_get(v_cases_2858_, 2);
lean_inc(v_discr_2860_);
v_alts_2861_ = lean_ctor_get(v_cases_2858_, 3);
lean_inc_ref(v_alts_2861_);
lean_dec_ref(v_cases_2858_);
lean_inc_ref(v_f_2820_);
v___x_2862_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2820_, v_resultType_2859_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref_known(v___x_2862_, 1);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2863_ = lean_apply_8(v_f_2820_, v_discr_2860_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2884_; 
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2863_, 0);
lean_dec(v_unused_2885_);
v___x_2865_ = v___x_2863_;
v_isShared_2866_ = v_isSharedCheck_2884_;
goto v_resetjp_2864_;
}
else
{
lean_dec(v___x_2863_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2884_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = lean_array_get_size(v_alts_2861_);
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_nat_dec_lt(v___x_2867_, v___x_2868_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref(v_alts_2861_);
lean_dec_ref(v_f_2820_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2869_);
v___x_2872_ = v___x_2865_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2869_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
else
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_nat_dec_le(v___x_2868_, v___x_2868_);
if (v___x_2874_ == 0)
{
if (v___x_2870_ == 0)
{
lean_object* v___x_2876_; 
lean_dec_ref(v_alts_2861_);
lean_dec_ref(v_f_2820_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2869_);
v___x_2876_ = v___x_2865_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2869_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
else
{
size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2865_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = lean_usize_of_nat(v___x_2868_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2819_, v_f_2820_, v_alts_2861_, v___x_2878_, v___x_2879_, v___x_2869_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec_ref(v_alts_2861_);
return v___x_2880_;
}
}
else
{
size_t v___x_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
lean_del_object(v___x_2865_);
v___x_2881_ = ((size_t)0ULL);
v___x_2882_ = lean_usize_of_nat(v___x_2868_);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2819_, v_f_2820_, v_alts_2861_, v___x_2881_, v___x_2882_, v___x_2869_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec_ref(v_alts_2861_);
return v___x_2883_;
}
}
}
}
else
{
lean_dec_ref(v_alts_2861_);
lean_dec_ref(v_f_2820_);
return v___x_2863_;
}
}
else
{
lean_dec_ref(v_alts_2861_);
lean_dec(v_discr_2860_);
lean_dec_ref(v_f_2820_);
return v___x_2862_;
}
}
case 5:
{
lean_object* v_fvarId_2886_; lean_object* v___x_2887_; 
v_fvarId_2886_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2886_);
lean_dec_ref_known(v_c_2821_, 1);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2887_ = lean_apply_8(v_f_2820_, v_fvarId_2886_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
return v___x_2887_;
}
case 6:
{
lean_object* v_type_2888_; lean_object* v___x_2889_; 
v_type_2888_ = lean_ctor_get(v_c_2821_, 0);
lean_inc_ref(v_type_2888_);
lean_dec_ref_known(v_c_2821_, 1);
v___x_2889_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2820_, v_type_2888_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2889_;
}
case 7:
{
lean_object* v_fvarId_2890_; lean_object* v_y_2891_; lean_object* v_k_2892_; lean_object* v___x_2893_; 
v_fvarId_2890_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2890_);
v_y_2891_ = lean_ctor_get(v_c_2821_, 2);
lean_inc(v_y_2891_);
v_k_2892_ = lean_ctor_get(v_c_2821_, 3);
lean_inc_ref(v_k_2892_);
lean_dec_ref_known(v_c_2821_, 4);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2893_ = lean_apply_8(v_f_2820_, v_fvarId_2890_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2893_, 1);
lean_inc_ref(v_f_2820_);
v___x_2894_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2820_, v_y_2891_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_dec_ref_known(v___x_2894_, 1);
v_c_2821_ = v_k_2892_;
goto _start;
}
else
{
lean_dec_ref(v_k_2892_);
lean_dec_ref(v_f_2820_);
return v___x_2894_;
}
}
else
{
lean_dec_ref(v_k_2892_);
lean_dec(v_y_2891_);
lean_dec_ref(v_f_2820_);
return v___x_2893_;
}
}
case 8:
{
lean_object* v_fvarId_2896_; lean_object* v_y_2897_; lean_object* v_k_2898_; lean_object* v___x_2899_; 
v_fvarId_2896_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2896_);
v_y_2897_ = lean_ctor_get(v_c_2821_, 2);
lean_inc(v_y_2897_);
v_k_2898_ = lean_ctor_get(v_c_2821_, 3);
lean_inc_ref(v_k_2898_);
lean_dec_ref_known(v_c_2821_, 4);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2899_ = lean_apply_8(v_f_2820_, v_fvarId_2896_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2900_; 
lean_dec_ref_known(v___x_2899_, 1);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2900_ = lean_apply_8(v_f_2820_, v_y_2897_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_dec_ref_known(v___x_2900_, 1);
v_c_2821_ = v_k_2898_;
goto _start;
}
else
{
lean_dec_ref(v_k_2898_);
lean_dec_ref(v_f_2820_);
return v___x_2900_;
}
}
else
{
lean_dec_ref(v_k_2898_);
lean_dec(v_y_2897_);
lean_dec_ref(v_f_2820_);
return v___x_2899_;
}
}
case 9:
{
lean_object* v_fvarId_2902_; lean_object* v_y_2903_; lean_object* v_ty_2904_; lean_object* v_k_2905_; lean_object* v___x_2906_; 
v_fvarId_2902_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2902_);
v_y_2903_ = lean_ctor_get(v_c_2821_, 3);
lean_inc(v_y_2903_);
v_ty_2904_ = lean_ctor_get(v_c_2821_, 4);
lean_inc_ref(v_ty_2904_);
v_k_2905_ = lean_ctor_get(v_c_2821_, 5);
lean_inc_ref(v_k_2905_);
lean_dec_ref_known(v_c_2821_, 6);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2906_ = lean_apply_8(v_f_2820_, v_fvarId_2902_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; 
lean_dec_ref_known(v___x_2906_, 1);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2907_ = lean_apply_8(v_f_2820_, v_y_2903_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2908_; 
lean_dec_ref_known(v___x_2907_, 1);
lean_inc_ref(v_f_2820_);
v___x_2908_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2820_, v_ty_2904_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_dec_ref_known(v___x_2908_, 1);
v_c_2821_ = v_k_2905_;
goto _start;
}
else
{
lean_dec_ref(v_k_2905_);
lean_dec_ref(v_f_2820_);
return v___x_2908_;
}
}
else
{
lean_dec_ref(v_k_2905_);
lean_dec_ref(v_ty_2904_);
lean_dec_ref(v_f_2820_);
return v___x_2907_;
}
}
else
{
lean_dec_ref(v_k_2905_);
lean_dec_ref(v_ty_2904_);
lean_dec(v_y_2903_);
lean_dec_ref(v_f_2820_);
return v___x_2906_;
}
}
case 10:
{
lean_object* v_fvarId_2910_; lean_object* v_k_2911_; lean_object* v___x_2912_; 
v_fvarId_2910_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2910_);
v_k_2911_ = lean_ctor_get(v_c_2821_, 2);
lean_inc_ref(v_k_2911_);
lean_dec_ref_known(v_c_2821_, 3);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2912_ = lean_apply_8(v_f_2820_, v_fvarId_2910_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref_known(v___x_2912_, 1);
v_c_2821_ = v_k_2911_;
goto _start;
}
else
{
lean_dec_ref(v_k_2911_);
lean_dec_ref(v_f_2820_);
return v___x_2912_;
}
}
case 11:
{
lean_object* v_fvarId_2914_; lean_object* v_k_2915_; lean_object* v___x_2916_; 
v_fvarId_2914_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2914_);
v_k_2915_ = lean_ctor_get(v_c_2821_, 2);
lean_inc_ref(v_k_2915_);
lean_dec_ref_known(v_c_2821_, 3);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2916_ = lean_apply_8(v_f_2820_, v_fvarId_2914_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_dec_ref_known(v___x_2916_, 1);
v_c_2821_ = v_k_2915_;
goto _start;
}
else
{
lean_dec_ref(v_k_2915_);
lean_dec_ref(v_f_2820_);
return v___x_2916_;
}
}
case 12:
{
lean_object* v_fvarId_2918_; lean_object* v_k_2919_; lean_object* v___x_2920_; 
v_fvarId_2918_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2918_);
v_k_2919_ = lean_ctor_get(v_c_2821_, 3);
lean_inc_ref(v_k_2919_);
lean_dec_ref_known(v_c_2821_, 4);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2920_ = lean_apply_8(v_f_2820_, v_fvarId_2918_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_dec_ref_known(v___x_2920_, 1);
v_c_2821_ = v_k_2919_;
goto _start;
}
else
{
lean_dec_ref(v_k_2919_);
lean_dec_ref(v_f_2820_);
return v___x_2920_;
}
}
case 13:
{
lean_object* v_fvarId_2922_; lean_object* v_k_2923_; lean_object* v___x_2924_; 
v_fvarId_2922_ = lean_ctor_get(v_c_2821_, 0);
lean_inc(v_fvarId_2922_);
v_k_2923_ = lean_ctor_get(v_c_2821_, 1);
lean_inc_ref(v_k_2923_);
lean_dec_ref_known(v_c_2821_, 2);
lean_inc_ref(v_f_2820_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v___y_2823_);
lean_inc(v___y_2822_);
v___x_2924_ = lean_apply_8(v_f_2820_, v_fvarId_2922_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_dec_ref_known(v___x_2924_, 1);
v_c_2821_ = v_k_2923_;
goto _start;
}
else
{
lean_dec_ref(v_k_2923_);
lean_dec_ref(v_f_2820_);
return v___x_2924_;
}
}
default: 
{
lean_object* v_decl_2926_; lean_object* v_k_2927_; lean_object* v_params_2928_; lean_object* v_type_2929_; lean_object* v_value_2930_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v_decl_2926_ = lean_ctor_get(v_c_2821_, 0);
lean_inc_ref(v_decl_2926_);
v_k_2927_ = lean_ctor_get(v_c_2821_, 1);
lean_inc_ref(v_k_2927_);
lean_dec_ref(v_c_2821_);
v_params_2928_ = lean_ctor_get(v_decl_2926_, 2);
lean_inc_ref(v_params_2928_);
v_type_2929_ = lean_ctor_get(v_decl_2926_, 3);
lean_inc_ref(v_type_2929_);
v_value_2930_ = lean_ctor_get(v_decl_2926_, 4);
lean_inc_ref(v_value_2930_);
lean_dec_ref(v_decl_2926_);
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = lean_array_get_size(v_params_2928_);
v___x_2943_ = lean_nat_dec_lt(v___x_2941_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec_ref(v_params_2928_);
lean_inc_ref(v_f_2820_);
v___x_2944_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2820_, v_type_2929_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v___x_2945_; 
lean_dec_ref_known(v___x_2944_, 1);
lean_inc_ref(v_f_2820_);
v___x_2945_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2819_, v_f_2820_, v_value_2930_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_dec_ref_known(v___x_2945_, 1);
v_c_2821_ = v_k_2927_;
goto _start;
}
else
{
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_f_2820_);
return v___x_2945_;
}
}
else
{
lean_dec_ref(v_value_2930_);
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_f_2820_);
return v___x_2944_;
}
}
else
{
lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_nat_dec_le(v___x_2942_, v___x_2942_);
if (v___x_2948_ == 0)
{
if (v___x_2943_ == 0)
{
lean_dec_ref(v_params_2928_);
v___y_2932_ = v___y_2822_;
v___y_2933_ = v___y_2823_;
v___y_2934_ = v___y_2824_;
v___y_2935_ = v___y_2825_;
v___y_2936_ = v___y_2826_;
v___y_2937_ = v___y_2827_;
goto v___jp_2931_;
}
else
{
size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___x_2942_);
lean_inc_ref(v_f_2820_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2819_, v_f_2820_, v_params_2928_, v___x_2949_, v___x_2950_, v___x_2947_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec_ref(v_params_2928_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_dec_ref_known(v___x_2951_, 1);
v___y_2932_ = v___y_2822_;
v___y_2933_ = v___y_2823_;
v___y_2934_ = v___y_2824_;
v___y_2935_ = v___y_2825_;
v___y_2936_ = v___y_2826_;
v___y_2937_ = v___y_2827_;
goto v___jp_2931_;
}
else
{
lean_dec_ref(v_value_2930_);
lean_dec_ref(v_type_2929_);
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_f_2820_);
return v___x_2951_;
}
}
}
else
{
size_t v___x_2952_; size_t v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = ((size_t)0ULL);
v___x_2953_ = lean_usize_of_nat(v___x_2942_);
lean_inc_ref(v_f_2820_);
v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2819_, v_f_2820_, v_params_2928_, v___x_2952_, v___x_2953_, v___x_2947_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec_ref(v_params_2928_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_dec_ref_known(v___x_2954_, 1);
v___y_2932_ = v___y_2822_;
v___y_2933_ = v___y_2823_;
v___y_2934_ = v___y_2824_;
v___y_2935_ = v___y_2825_;
v___y_2936_ = v___y_2826_;
v___y_2937_ = v___y_2827_;
goto v___jp_2931_;
}
else
{
lean_dec_ref(v_value_2930_);
lean_dec_ref(v_type_2929_);
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_f_2820_);
return v___x_2954_;
}
}
}
v___jp_2931_:
{
lean_object* v___x_2938_; 
lean_inc_ref(v_f_2820_);
v___x_2938_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2820_, v_type_2929_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2939_; 
lean_dec_ref_known(v___x_2938_, 1);
lean_inc_ref(v_f_2820_);
v___x_2939_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2819_, v_f_2820_, v_value_2930_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_dec_ref_known(v___x_2939_, 1);
v_c_2821_ = v_k_2927_;
v___y_2822_ = v___y_2932_;
v___y_2823_ = v___y_2933_;
v___y_2824_ = v___y_2934_;
v___y_2825_ = v___y_2935_;
v___y_2826_ = v___y_2936_;
v___y_2827_ = v___y_2937_;
goto _start;
}
else
{
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_f_2820_);
return v___x_2939_;
}
}
else
{
lean_dec_ref(v_value_2930_);
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_f_2820_);
return v___x_2938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2955_, lean_object* v_f_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2955_, v_f_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_2966_, lean_object* v_f_2967_, lean_object* v_as_2968_, lean_object* v_i_2969_, lean_object* v_stop_2970_, lean_object* v_b_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v_pu_boxed_2979_; size_t v_i_boxed_2980_; size_t v_stop_boxed_2981_; lean_object* v_res_2982_; 
v_pu_boxed_2979_ = lean_unbox(v_pu_2966_);
v_i_boxed_2980_ = lean_unbox_usize(v_i_2969_);
lean_dec(v_i_2969_);
v_stop_boxed_2981_ = lean_unbox_usize(v_stop_2970_);
lean_dec(v_stop_2970_);
v_res_2982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_2979_, v_f_2967_, v_as_2968_, v_i_boxed_2980_, v_stop_boxed_2981_, v_b_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v_as_2968_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_2983_, lean_object* v_f_2984_, lean_object* v_c_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v_pu_boxed_2993_; lean_object* v_res_2994_; 
v_pu_boxed_2993_ = lean_unbox(v_pu_2983_);
v_res_2994_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_2993_, v_f_2984_, v_c_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_2995_, lean_object* v_f_2996_, lean_object* v_decl_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_params_3005_; lean_object* v_type_3006_; lean_object* v_value_3007_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_params_3005_ = lean_ctor_get(v_decl_2997_, 2);
lean_inc_ref(v_params_3005_);
v_type_3006_ = lean_ctor_get(v_decl_2997_, 3);
lean_inc_ref(v_type_3006_);
v_value_3007_ = lean_ctor_get(v_decl_2997_, 4);
lean_inc_ref(v_value_3007_);
lean_dec_ref(v_decl_2997_);
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3018_ = lean_array_get_size(v_params_3005_);
v___x_3019_ = lean_nat_dec_lt(v___x_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
lean_dec_ref(v_params_3005_);
lean_inc_ref(v_f_2996_);
v___x_3020_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2996_, v_type_3006_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3021_; 
lean_dec_ref_known(v___x_3020_, 1);
v___x_3021_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2995_, v_f_2996_, v_value_3007_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
return v___x_3021_;
}
else
{
lean_dec_ref(v_value_3007_);
lean_dec_ref(v_f_2996_);
return v___x_3020_;
}
}
else
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = lean_nat_dec_le(v___x_3018_, v___x_3018_);
if (v___x_3023_ == 0)
{
if (v___x_3019_ == 0)
{
lean_dec_ref(v_params_3005_);
v___y_3009_ = v___y_2998_;
v___y_3010_ = v___y_2999_;
v___y_3011_ = v___y_3000_;
v___y_3012_ = v___y_3001_;
v___y_3013_ = v___y_3002_;
v___y_3014_ = v___y_3003_;
goto v___jp_3008_;
}
else
{
size_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = lean_usize_of_nat(v___x_3018_);
lean_inc_ref(v_f_2996_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2995_, v_f_2996_, v_params_3005_, v___x_3024_, v___x_3025_, v___x_3022_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec_ref(v_params_3005_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_dec_ref_known(v___x_3026_, 1);
v___y_3009_ = v___y_2998_;
v___y_3010_ = v___y_2999_;
v___y_3011_ = v___y_3000_;
v___y_3012_ = v___y_3001_;
v___y_3013_ = v___y_3002_;
v___y_3014_ = v___y_3003_;
goto v___jp_3008_;
}
else
{
lean_dec_ref(v_value_3007_);
lean_dec_ref(v_type_3006_);
lean_dec_ref(v_f_2996_);
return v___x_3026_;
}
}
}
else
{
size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = ((size_t)0ULL);
v___x_3028_ = lean_usize_of_nat(v___x_3018_);
lean_inc_ref(v_f_2996_);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2995_, v_f_2996_, v_params_3005_, v___x_3027_, v___x_3028_, v___x_3022_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec_ref(v_params_3005_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_dec_ref_known(v___x_3029_, 1);
v___y_3009_ = v___y_2998_;
v___y_3010_ = v___y_2999_;
v___y_3011_ = v___y_3000_;
v___y_3012_ = v___y_3001_;
v___y_3013_ = v___y_3002_;
v___y_3014_ = v___y_3003_;
goto v___jp_3008_;
}
else
{
lean_dec_ref(v_value_3007_);
lean_dec_ref(v_type_3006_);
lean_dec_ref(v_f_2996_);
return v___x_3029_;
}
}
}
v___jp_3008_:
{
lean_object* v___x_3015_; 
lean_inc_ref(v_f_2996_);
v___x_3015_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2996_, v_type_3006_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v___x_3016_; 
lean_dec_ref_known(v___x_3015_, 1);
v___x_3016_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2995_, v_f_2996_, v_value_3007_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
return v___x_3016_;
}
else
{
lean_dec_ref(v_value_3007_);
lean_dec_ref(v_f_2996_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_3030_, lean_object* v_f_3031_, lean_object* v_decl_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
uint8_t v_pu_boxed_3040_; lean_object* v_res_3041_; 
v_pu_boxed_3040_ = lean_unbox(v_pu_3030_);
v_res_3041_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_3040_, v_f_3031_, v_decl_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_3042_){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_box(0);
v___x_3044_ = lean_panic_fn_borrowed(v___x_3043_, v_msg_3042_);
return v___x_3044_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3048_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_3049_ = lean_unsigned_to_nat(11u);
v___x_3050_ = lean_unsigned_to_nat(163u);
v___x_3051_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_3052_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_3053_ = l_mkPanicMessageWithDecl(v___x_3052_, v___x_3051_, v___x_3050_, v___x_3049_, v___x_3048_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_3054_, lean_object* v_x_3055_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3057_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_3056_);
return v___x_3057_;
}
else
{
lean_object* v_key_3058_; lean_object* v_value_3059_; lean_object* v_tail_3060_; uint8_t v___x_3061_; 
v_key_3058_ = lean_ctor_get(v_x_3055_, 0);
v_value_3059_ = lean_ctor_get(v_x_3055_, 1);
v_tail_3060_ = lean_ctor_get(v_x_3055_, 2);
v___x_3061_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_3058_, v_a_3054_);
if (v___x_3061_ == 0)
{
v_x_3055_ = v_tail_3060_;
goto _start;
}
else
{
lean_inc(v_value_3059_);
return v_value_3059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_3063_, lean_object* v_x_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3063_, v_x_3064_);
lean_dec(v_x_3064_);
lean_dec(v_a_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_buckets_3068_; lean_object* v___x_3069_; uint64_t v___x_3070_; uint64_t v___x_3071_; uint64_t v___x_3072_; uint64_t v_fold_3073_; uint64_t v___x_3074_; uint64_t v___x_3075_; uint64_t v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_buckets_3068_ = lean_ctor_get(v_m_3066_, 1);
v___x_3069_ = lean_array_get_size(v_buckets_3068_);
v___x_3070_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_3067_);
v___x_3071_ = 32ULL;
v___x_3072_ = lean_uint64_shift_right(v___x_3070_, v___x_3071_);
v_fold_3073_ = lean_uint64_xor(v___x_3070_, v___x_3072_);
v___x_3074_ = 16ULL;
v___x_3075_ = lean_uint64_shift_right(v_fold_3073_, v___x_3074_);
v___x_3076_ = lean_uint64_xor(v_fold_3073_, v___x_3075_);
v___x_3077_ = lean_uint64_to_usize(v___x_3076_);
v___x_3078_ = lean_usize_of_nat(v___x_3069_);
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_sub(v___x_3078_, v___x_3079_);
v___x_3081_ = lean_usize_land(v___x_3077_, v___x_3080_);
v___x_3082_ = lean_array_uget_borrowed(v_buckets_3068_, v___x_3081_);
v___x_3083_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3067_, v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3084_, v_a_3085_);
lean_dec(v_a_3085_);
lean_dec_ref(v_m_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v___y_3097_; uint8_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = 0;
v___x_3123_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3088_))
{
case 0:
{
lean_object* v_decl_3124_; lean_object* v___x_3125_; 
v_decl_3124_ = lean_ctor_get(v_decl_3088_, 0);
lean_inc_ref(v_decl_3124_);
v___x_3125_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3122_, v___x_3123_, v_decl_3124_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
v___y_3097_ = v___x_3125_;
goto v___jp_3096_;
}
case 1:
{
lean_object* v_decl_3126_; lean_object* v___x_3127_; 
v_decl_3126_ = lean_ctor_get(v_decl_3088_, 0);
lean_inc_ref(v_decl_3126_);
v___x_3127_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3122_, v___x_3123_, v_decl_3126_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
v___y_3097_ = v___x_3127_;
goto v___jp_3096_;
}
case 2:
{
lean_object* v_decl_3128_; lean_object* v___x_3129_; 
v_decl_3128_ = lean_ctor_get(v_decl_3088_, 0);
lean_inc_ref(v_decl_3128_);
v___x_3129_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3122_, v___x_3123_, v_decl_3128_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
v___y_3097_ = v___x_3129_;
goto v___jp_3096_;
}
case 3:
{
lean_object* v_fvarId_3130_; lean_object* v_y_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_fvarId_3130_ = lean_ctor_get(v_decl_3088_, 0);
v_y_3131_ = lean_ctor_get(v_decl_3088_, 2);
lean_inc(v_fvarId_3130_);
v___x_3132_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3130_, v_a_3089_);
lean_dec_ref(v___x_3132_);
lean_inc(v_y_3131_);
v___x_3133_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3123_, v_y_3131_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
v___y_3097_ = v___x_3133_;
goto v___jp_3096_;
}
case 4:
{
lean_object* v_fvarId_3134_; lean_object* v_y_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_fvarId_3134_ = lean_ctor_get(v_decl_3088_, 0);
v_y_3135_ = lean_ctor_get(v_decl_3088_, 2);
lean_inc(v_fvarId_3134_);
v___x_3136_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3134_, v_a_3089_);
lean_dec_ref(v___x_3136_);
lean_inc(v_y_3135_);
v___x_3137_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3135_, v_a_3089_);
v___y_3097_ = v___x_3137_;
goto v___jp_3096_;
}
case 5:
{
lean_object* v_fvarId_3138_; lean_object* v_y_3139_; lean_object* v_ty_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_fvarId_3138_ = lean_ctor_get(v_decl_3088_, 0);
v_y_3139_ = lean_ctor_get(v_decl_3088_, 3);
v_ty_3140_ = lean_ctor_get(v_decl_3088_, 4);
lean_inc(v_fvarId_3138_);
v___x_3141_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3138_, v_a_3089_);
lean_dec_ref(v___x_3141_);
lean_inc(v_y_3139_);
v___x_3142_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3139_, v_a_3089_);
lean_dec_ref(v___x_3142_);
lean_inc_ref(v_ty_3140_);
v___x_3143_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3123_, v_ty_3140_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
v___y_3097_ = v___x_3143_;
goto v___jp_3096_;
}
default: 
{
lean_object* v_fvarId_3144_; lean_object* v___x_3145_; 
v_fvarId_3144_ = lean_ctor_get(v_decl_3088_, 0);
lean_inc(v_fvarId_3144_);
v___x_3145_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3144_, v_a_3089_);
v___y_3097_ = v___x_3145_;
goto v___jp_3096_;
}
}
v___jp_3096_:
{
if (lean_obj_tag(v___y_3097_) == 0)
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3120_; 
v_isSharedCheck_3120_ = !lean_is_exclusive(v___y_3097_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v___y_3097_, 0);
lean_dec(v_unused_3121_);
v___x_3099_ = v___y_3097_;
v_isShared_3100_ = v_isSharedCheck_3120_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v___y_3097_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3120_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v_decision_3102_; lean_object* v_newArms_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3119_; 
v___x_3101_ = lean_st_ref_take(v_a_3089_);
v_decision_3102_ = lean_ctor_get(v___x_3101_, 0);
v_newArms_3103_ = lean_ctor_get(v___x_3101_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3105_ = v___x_3101_;
v_isShared_3106_ = v_isSharedCheck_3119_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_newArms_3103_);
lean_inc(v_decision_3102_);
lean_dec(v___x_3101_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3119_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3107_ = lean_box(2);
v___x_3108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3103_, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_decl_3088_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3103_, v___x_3107_, v___x_3109_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v___x_3110_);
v___x_3112_ = v___x_3105_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_decision_3102_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3113_ = lean_st_ref_set(v_a_3089_, v___x_3112_);
v___x_3114_ = lean_box(0);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3114_);
v___x_3116_ = v___x_3099_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3088_);
return v___y_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec(v_a_3147_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3155_, lean_object* v_f_3156_, lean_object* v_arg_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3156_, v_arg_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3166_, lean_object* v_f_3167_, lean_object* v_arg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v_pu_boxed_3176_; lean_object* v_res_3177_; 
v_pu_boxed_3176_ = lean_unbox(v_pu_3166_);
v_res_3177_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3176_, v_f_3167_, v_arg_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3178_, lean_object* v_f_3179_, lean_object* v_param_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3179_, v_param_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3189_, lean_object* v_f_3190_, lean_object* v_param_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
uint8_t v_pu_boxed_3199_; lean_object* v_res_3200_; 
v_pu_boxed_3199_ = lean_unbox(v_pu_3189_);
v_res_3200_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3199_, v_f_3190_, v_param_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec(v___y_3192_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3201_, lean_object* v_alt_3202_, lean_object* v_f_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3202_, v_f_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3212_, lean_object* v_alt_3213_, lean_object* v_f_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v_pu_boxed_3222_; lean_object* v_res_3223_; 
v_pu_boxed_3222_ = lean_unbox(v_pu_3212_);
v_res_3223_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3222_, v_alt_3213_, v_f_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec(v___y_3215_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3224_, lean_object* v_arm_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3228_; lean_object* v_decision_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_st_ref_get(v_a_3226_);
v_decision_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc_ref(v_decision_3229_);
lean_dec(v___x_3228_);
v___x_3230_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3229_, v_fvar_3224_);
lean_dec_ref(v_decision_3229_);
if (lean_obj_tag(v___x_3230_) == 1)
{
lean_object* v_val_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3276_; 
v_val_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3276_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_val_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3276_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = lean_box(3);
v___x_3236_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3231_, v___x_3235_);
if (v___x_3236_ == 0)
{
uint8_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3231_, v_arm_3225_);
lean_dec(v_arm_3225_);
lean_dec(v_val_3231_);
v___x_3238_ = lean_bool_not(v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
lean_dec(v_fvar_3224_);
v___x_3239_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3239_);
v___x_3241_ = v___x_3233_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
else
{
lean_object* v___x_3243_; lean_object* v_decision_3244_; lean_object* v_newArms_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3259_; 
v___x_3243_ = lean_st_ref_take(v_a_3226_);
v_decision_3244_ = lean_ctor_get(v___x_3243_, 0);
v_newArms_3245_ = lean_ctor_get(v___x_3243_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3247_ = v___x_3243_;
v_isShared_3248_ = v_isSharedCheck_3259_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_newArms_3245_);
lean_inc(v_decision_3244_);
lean_dec(v___x_3243_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3259_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3249_ = lean_box(2);
v___x_3250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3244_, v_fvar_3224_, v___x_3249_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3250_);
v___x_3252_ = v___x_3247_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_newArms_3245_);
v___x_3252_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3253_ = lean_st_ref_set(v_a_3226_, v___x_3252_);
v___x_3254_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3254_);
v___x_3256_ = v___x_3233_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_object* v___x_3260_; lean_object* v_decision_3261_; lean_object* v_newArms_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3275_; 
lean_dec(v_val_3231_);
v___x_3260_ = lean_st_ref_take(v_a_3226_);
v_decision_3261_ = lean_ctor_get(v___x_3260_, 0);
v_newArms_3262_ = lean_ctor_get(v___x_3260_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3264_ = v___x_3260_;
v_isShared_3265_ = v_isSharedCheck_3275_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_newArms_3262_);
lean_inc(v_decision_3261_);
lean_dec(v___x_3260_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3275_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3261_, v_fvar_3224_, v_arm_3225_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_newArms_3262_);
v___x_3268_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3269_ = lean_st_ref_set(v_a_3226_, v___x_3268_);
v___x_3270_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3270_);
v___x_3272_ = v___x_3233_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec(v___x_3230_);
lean_dec(v_arm_3225_);
lean_dec(v_fvar_3224_);
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3279_, lean_object* v_arm_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3279_, v_arm_3280_, v_a_3281_);
lean_dec(v_a_3281_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3284_, lean_object* v_arm_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3284_, v_arm_3285_, v_a_3286_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3294_, lean_object* v_arm_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3294_, v_arm_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec(v_a_3296_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3304_, lean_object* v_x_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3305_, v___x_3304_, v___y_3306_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec(v___y_3316_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3326_ = lean_panic_fn_borrowed(v___x_3325_, v_msg_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3327_, lean_object* v_x_3328_){
_start:
{
if (lean_obj_tag(v_x_3328_) == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3330_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3329_);
return v___x_3330_;
}
else
{
lean_object* v_key_3331_; lean_object* v_value_3332_; lean_object* v_tail_3333_; uint8_t v___x_3334_; 
v_key_3331_ = lean_ctor_get(v_x_3328_, 0);
v_value_3332_ = lean_ctor_get(v_x_3328_, 1);
v_tail_3333_ = lean_ctor_get(v_x_3328_, 2);
v___x_3334_ = l_Lean_instBEqFVarId_beq(v_key_3331_, v_a_3327_);
if (v___x_3334_ == 0)
{
v_x_3328_ = v_tail_3333_;
goto _start;
}
else
{
lean_inc(v_value_3332_);
return v_value_3332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3336_, v_x_3337_);
lean_dec(v_x_3337_);
lean_dec(v_a_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_buckets_3341_; lean_object* v___x_3342_; uint64_t v___x_3343_; uint64_t v___x_3344_; uint64_t v___x_3345_; uint64_t v_fold_3346_; uint64_t v___x_3347_; uint64_t v___x_3348_; uint64_t v___x_3349_; size_t v___x_3350_; size_t v___x_3351_; size_t v___x_3352_; size_t v___x_3353_; size_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_buckets_3341_ = lean_ctor_get(v_m_3339_, 1);
v___x_3342_ = lean_array_get_size(v_buckets_3341_);
v___x_3343_ = l_Lean_instHashableFVarId_hash(v_a_3340_);
v___x_3344_ = 32ULL;
v___x_3345_ = lean_uint64_shift_right(v___x_3343_, v___x_3344_);
v_fold_3346_ = lean_uint64_xor(v___x_3343_, v___x_3345_);
v___x_3347_ = 16ULL;
v___x_3348_ = lean_uint64_shift_right(v_fold_3346_, v___x_3347_);
v___x_3349_ = lean_uint64_xor(v_fold_3346_, v___x_3348_);
v___x_3350_ = lean_uint64_to_usize(v___x_3349_);
v___x_3351_ = lean_usize_of_nat(v___x_3342_);
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = lean_usize_sub(v___x_3351_, v___x_3352_);
v___x_3354_ = lean_usize_land(v___x_3350_, v___x_3353_);
v___x_3355_ = lean_array_uget_borrowed(v_buckets_3341_, v___x_3354_);
v___x_3356_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3340_, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_m_3357_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v___x_3368_; lean_object* v_decision_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3426_; 
v___x_3368_ = lean_st_ref_get(v_a_3361_);
v_decision_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v___x_3368_, 1);
lean_dec(v_unused_3427_);
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3426_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_decision_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3426_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___y_3377_; lean_object* v___f_3403_; 
v___x_3373_ = 0;
v___x_3374_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3360_);
v___x_3375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3369_, v___x_3374_);
lean_dec(v___x_3374_);
lean_dec_ref(v_decision_3369_);
lean_inc(v___x_3375_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3403_, 0, v___x_3375_);
switch(lean_obj_tag(v_decl_3360_))
{
case 0:
{
lean_object* v_decl_3404_; lean_object* v___x_3405_; 
v_decl_3404_ = lean_ctor_get(v_decl_3360_, 0);
lean_inc_ref(v_decl_3404_);
v___x_3405_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3373_, v___f_3403_, v_decl_3404_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
v___y_3377_ = v___x_3405_;
goto v___jp_3376_;
}
case 1:
{
lean_object* v_decl_3406_; lean_object* v___x_3407_; 
v_decl_3406_ = lean_ctor_get(v_decl_3360_, 0);
lean_inc_ref(v_decl_3406_);
v___x_3407_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3373_, v___f_3403_, v_decl_3406_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
v___y_3377_ = v___x_3407_;
goto v___jp_3376_;
}
case 2:
{
lean_object* v_decl_3408_; lean_object* v___x_3409_; 
v_decl_3408_ = lean_ctor_get(v_decl_3360_, 0);
lean_inc_ref(v_decl_3408_);
v___x_3409_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3373_, v___f_3403_, v_decl_3408_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
v___y_3377_ = v___x_3409_;
goto v___jp_3376_;
}
case 3:
{
lean_object* v_fvarId_3410_; lean_object* v_y_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_fvarId_3410_ = lean_ctor_get(v_decl_3360_, 0);
v_y_3411_ = lean_ctor_get(v_decl_3360_, 2);
lean_inc(v___x_3375_);
lean_inc(v_fvarId_3410_);
v___x_3412_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3410_, v___x_3375_, v_a_3361_);
lean_dec_ref(v___x_3412_);
lean_inc(v_y_3411_);
v___x_3413_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3403_, v_y_3411_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
v___y_3377_ = v___x_3413_;
goto v___jp_3376_;
}
case 4:
{
lean_object* v_fvarId_3414_; lean_object* v_y_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec_ref(v___f_3403_);
v_fvarId_3414_ = lean_ctor_get(v_decl_3360_, 0);
v_y_3415_ = lean_ctor_get(v_decl_3360_, 2);
lean_inc_n(v___x_3375_, 2);
lean_inc(v_fvarId_3414_);
v___x_3416_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3414_, v___x_3375_, v_a_3361_);
lean_dec_ref(v___x_3416_);
lean_inc(v_y_3415_);
v___x_3417_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3415_, v___x_3375_, v_a_3361_);
v___y_3377_ = v___x_3417_;
goto v___jp_3376_;
}
case 5:
{
lean_object* v_fvarId_3418_; lean_object* v_y_3419_; lean_object* v_ty_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_fvarId_3418_ = lean_ctor_get(v_decl_3360_, 0);
v_y_3419_ = lean_ctor_get(v_decl_3360_, 3);
v_ty_3420_ = lean_ctor_get(v_decl_3360_, 4);
lean_inc_n(v___x_3375_, 2);
lean_inc(v_fvarId_3418_);
v___x_3421_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3418_, v___x_3375_, v_a_3361_);
lean_dec_ref(v___x_3421_);
lean_inc(v_y_3419_);
v___x_3422_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3419_, v___x_3375_, v_a_3361_);
lean_dec_ref(v___x_3422_);
lean_inc_ref(v_ty_3420_);
v___x_3423_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3403_, v_ty_3420_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
v___y_3377_ = v___x_3423_;
goto v___jp_3376_;
}
default: 
{
lean_object* v_fvarId_3424_; lean_object* v___x_3425_; 
lean_dec_ref(v___f_3403_);
v_fvarId_3424_ = lean_ctor_get(v_decl_3360_, 0);
lean_inc(v___x_3375_);
lean_inc(v_fvarId_3424_);
v___x_3425_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3424_, v___x_3375_, v_a_3361_);
v___y_3377_ = v___x_3425_;
goto v___jp_3376_;
}
}
v___jp_3376_:
{
if (lean_obj_tag(v___y_3377_) == 0)
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3401_; 
v_isSharedCheck_3401_ = !lean_is_exclusive(v___y_3377_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v___y_3377_, 0);
lean_dec(v_unused_3402_);
v___x_3379_ = v___y_3377_;
v_isShared_3380_ = v_isSharedCheck_3401_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v___y_3377_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3401_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v_decision_3382_; lean_object* v_newArms_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3400_; 
v___x_3381_ = lean_st_ref_take(v_a_3361_);
v_decision_3382_ = lean_ctor_get(v___x_3381_, 0);
v_newArms_3383_ = lean_ctor_get(v___x_3381_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3385_ = v___x_3381_;
v_isShared_3386_ = v_isSharedCheck_3400_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_newArms_3383_);
lean_inc(v_decision_3382_);
lean_dec(v___x_3381_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3400_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3383_, v___x_3375_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 1);
lean_ctor_set(v___x_3371_, 1, v___x_3387_);
lean_ctor_set(v___x_3371_, 0, v_decl_3360_);
v___x_3389_ = v___x_3371_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_decl_3360_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3383_, v___x_3375_, v___x_3389_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 1, v___x_3390_);
v___x_3392_ = v___x_3385_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_decision_3382_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3393_ = lean_st_ref_set(v_a_3361_, v___x_3392_);
v___x_3394_ = lean_box(0);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3394_);
v___x_3396_ = v___x_3379_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3375_);
lean_del_object(v___x_3371_);
lean_dec_ref(v_decl_3360_);
return v___y_3377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec(v_a_3429_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3437_, lean_object* v_b_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
if (lean_obj_tag(v_as_x27_3437_) == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_b_3438_);
return v___x_3446_;
}
else
{
lean_object* v_head_3447_; lean_object* v_tail_3448_; lean_object* v___x_3449_; lean_object* v_decision_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v_head_3447_ = lean_ctor_get(v_as_x27_3437_, 0);
v_tail_3448_ = lean_ctor_get(v_as_x27_3437_, 1);
v___x_3449_ = lean_st_ref_get(v___y_3439_);
v_decision_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc_ref(v_decision_3450_);
lean_dec(v___x_3449_);
v___x_3451_ = lean_box(0);
v___x_3452_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3447_);
v___x_3453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3450_, v___x_3452_);
lean_dec(v___x_3452_);
lean_dec_ref(v_decision_3450_);
v___x_3454_ = lean_box(3);
v___x_3455_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = lean_box(2);
v___x_3457_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3453_, v___x_3456_);
lean_dec(v___x_3453_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_inc(v_head_3447_);
v___x_3458_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3447_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_dec_ref_known(v___x_3458_, 1);
v_as_x27_3437_ = v_tail_3448_;
v_b_3438_ = v___x_3451_;
goto _start;
}
else
{
return v___x_3458_;
}
}
else
{
lean_object* v___x_3460_; 
lean_inc(v_head_3447_);
v___x_3460_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3447_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_dec_ref_known(v___x_3460_, 1);
v_as_x27_3437_ = v_tail_3448_;
v_b_3438_ = v___x_3451_;
goto _start;
}
else
{
return v___x_3460_;
}
}
}
else
{
uint8_t v___x_3462_; lean_object* v___x_3463_; 
lean_dec(v___x_3453_);
v___x_3462_ = 0;
v___x_3463_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3462_, v_head_3447_, v___y_3442_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_dec_ref_known(v___x_3463_, 1);
v_as_x27_3437_ = v_tail_3448_;
v_b_3438_ = v___x_3451_;
goto _start;
}
else
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3465_, lean_object* v_b_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3465_, v_b_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v_as_x27_3465_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = lean_box(0);
v___x_3483_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3476_, v___x_3482_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v___x_3483_, 0);
lean_dec(v_unused_3491_);
v___x_3485_ = v___x_3483_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v___x_3483_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3482_);
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3482_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
else
{
return v___x_3483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec(v_a_3492_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3500_, lean_object* v_as_x27_3501_, lean_object* v_b_3502_, lean_object* v_a_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3501_, v_b_3502_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_3512_, lean_object* v_as_x27_3513_, lean_object* v_b_3514_, lean_object* v_a_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3512_, v_as_x27_3513_, v_b_3514_, v_a_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v_as_x27_3513_);
lean_dec(v_as_3512_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3528_ = lean_unsigned_to_nat(0u);
v___x_3529_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
lean_ctor_set(v___x_3529_, 2, v___x_3528_);
lean_ctor_set(v___x_3529_, 3, v___x_3528_);
lean_ctor_set(v___x_3529_, 4, v___x_3527_);
lean_ctor_set(v___x_3529_, 5, v___x_3527_);
lean_ctor_set(v___x_3529_, 6, v___x_3527_);
lean_ctor_set(v___x_3529_, 7, v___x_3527_);
lean_ctor_set(v___x_3529_, 8, v___x_3527_);
lean_ctor_set(v___x_3529_, 9, v___x_3527_);
return v___x_3529_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3530_; double v___x_3531_; 
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = lean_float_of_nat(v___x_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3535_, lean_object* v_msg_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_options_3542_; lean_object* v_ref_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_options_3542_ = lean_ctor_get(v___y_3539_, 2);
v_ref_3543_ = lean_ctor_get(v___y_3539_, 5);
v___x_3544_ = lean_st_ref_get(v___y_3540_);
v___x_3545_ = lean_st_ref_get(v___y_3538_);
v___x_3546_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3537_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3605_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3605_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3605_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v_env_3551_; lean_object* v_lctx_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3603_; 
v_env_3551_ = lean_ctor_get(v___x_3544_, 0);
lean_inc_ref(v_env_3551_);
lean_dec(v___x_3544_);
v_lctx_3552_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3545_, 1);
lean_dec(v_unused_3604_);
v___x_3554_ = v___x_3545_;
v_isShared_3555_ = v_isSharedCheck_3603_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_lctx_3552_);
lean_dec(v___x_3545_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3603_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v_traceState_3558_; lean_object* v_env_3559_; lean_object* v_nextMacroScope_3560_; lean_object* v_ngen_3561_; lean_object* v_auxDeclNGen_3562_; lean_object* v_cache_3563_; lean_object* v_messages_3564_; lean_object* v_infoState_3565_; lean_object* v_snapshotTasks_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3602_; 
v___x_3556_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3557_ = lean_st_ref_take(v___y_3540_);
v_traceState_3558_ = lean_ctor_get(v___x_3557_, 4);
v_env_3559_ = lean_ctor_get(v___x_3557_, 0);
v_nextMacroScope_3560_ = lean_ctor_get(v___x_3557_, 1);
v_ngen_3561_ = lean_ctor_get(v___x_3557_, 2);
v_auxDeclNGen_3562_ = lean_ctor_get(v___x_3557_, 3);
v_cache_3563_ = lean_ctor_get(v___x_3557_, 5);
v_messages_3564_ = lean_ctor_get(v___x_3557_, 6);
v_infoState_3565_ = lean_ctor_get(v___x_3557_, 7);
v_snapshotTasks_3566_ = lean_ctor_get(v___x_3557_, 8);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3568_ = v___x_3557_;
v_isShared_3569_ = v_isSharedCheck_3602_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_snapshotTasks_3566_);
lean_inc(v_infoState_3565_);
lean_inc(v_messages_3564_);
lean_inc(v_cache_3563_);
lean_inc(v_traceState_3558_);
lean_inc(v_auxDeclNGen_3562_);
lean_inc(v_ngen_3561_);
lean_inc(v_nextMacroScope_3560_);
lean_inc(v_env_3559_);
lean_dec(v___x_3557_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3602_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
uint64_t v_tid_3570_; lean_object* v_traces_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3601_; 
v_tid_3570_ = lean_ctor_get_uint64(v_traceState_3558_, sizeof(void*)*1);
v_traces_3571_ = lean_ctor_get(v_traceState_3558_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_traceState_3558_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3573_ = v_traceState_3558_;
v_isShared_3574_ = v_isSharedCheck_3601_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_traces_3571_);
lean_dec(v_traceState_3558_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3601_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3575_ = lean_unbox(v_a_3547_);
lean_dec(v_a_3547_);
v___x_3576_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3552_, v___x_3575_);
lean_dec_ref(v_lctx_3552_);
lean_inc_ref(v_options_3542_);
v___x_3577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3577_, 0, v_env_3551_);
lean_ctor_set(v___x_3577_, 1, v___x_3556_);
lean_ctor_set(v___x_3577_, 2, v___x_3576_);
lean_ctor_set(v___x_3577_, 3, v_options_3542_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set_tag(v___x_3554_, 3);
lean_ctor_set(v___x_3554_, 1, v_msg_3536_);
lean_ctor_set(v___x_3554_, 0, v___x_3577_);
v___x_3579_ = v___x_3554_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_msg_3536_);
v___x_3579_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; double v___x_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3580_ = lean_box(0);
v___x_3581_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3582_ = 0;
v___x_3583_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3584_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3584_, 0, v_cls_3535_);
lean_ctor_set(v___x_3584_, 1, v___x_3580_);
lean_ctor_set(v___x_3584_, 2, v___x_3583_);
lean_ctor_set_float(v___x_3584_, sizeof(void*)*3, v___x_3581_);
lean_ctor_set_float(v___x_3584_, sizeof(void*)*3 + 8, v___x_3581_);
lean_ctor_set_uint8(v___x_3584_, sizeof(void*)*3 + 16, v___x_3582_);
v___x_3585_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3586_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3579_);
lean_ctor_set(v___x_3586_, 2, v___x_3585_);
lean_inc(v_ref_3543_);
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v_ref_3543_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = l_Lean_PersistentArray_push___redArg(v_traces_3571_, v___x_3587_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3588_);
v___x_3590_ = v___x_3573_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3588_);
lean_ctor_set_uint64(v_reuseFailAlloc_3599_, sizeof(void*)*1, v_tid_3570_);
v___x_3590_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 4, v___x_3590_);
v___x_3592_ = v___x_3568_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_env_3559_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_nextMacroScope_3560_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_ngen_3561_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_auxDeclNGen_3562_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3598_, 5, v_cache_3563_);
lean_ctor_set(v_reuseFailAlloc_3598_, 6, v_messages_3564_);
lean_ctor_set(v_reuseFailAlloc_3598_, 7, v_infoState_3565_);
lean_ctor_set(v_reuseFailAlloc_3598_, 8, v_snapshotTasks_3566_);
v___x_3592_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = lean_st_ref_set(v___y_3540_, v___x_3592_);
v___x_3594_ = lean_box(0);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3594_);
v___x_3596_ = v___x_3549_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
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
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v___x_3545_);
lean_dec(v___x_3544_);
lean_dec_ref(v_msg_3536_);
lean_dec(v_cls_3535_);
v_a_3606_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3546_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3546_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3614_, lean_object* v_msg_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3614_, v_msg_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3622_, lean_object* v_msg_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3622_, v_msg_3623_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3631_, lean_object* v_msg_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3631_, v_msg_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
return v_res_3639_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3649_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3650_ = l_Lean_Name_append(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
switch(lean_obj_tag(v_code_3657_))
{
case 0:
{
lean_object* v_decl_3664_; lean_object* v_k_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_decl_3664_ = lean_ctor_get(v_code_3657_, 0);
lean_inc_ref(v_decl_3664_);
v_k_3665_ = lean_ctor_get(v_code_3657_, 1);
lean_inc_ref(v_k_3665_);
lean_dec_ref_known(v_code_3657_, 2);
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v_decl_3664_);
v___x_3667_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3667_, 0, v_k_3665_);
v___x_3668_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3666_, v___x_3667_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
return v___x_3668_;
}
case 1:
{
lean_object* v_decl_3669_; lean_object* v_k_3670_; lean_object* v_params_3671_; lean_object* v_type_3672_; lean_object* v_value_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v_decl_3669_ = lean_ctor_get(v_code_3657_, 0);
lean_inc_ref(v_decl_3669_);
v_k_3670_ = lean_ctor_get(v_code_3657_, 1);
lean_inc_ref(v_k_3670_);
lean_dec_ref_known(v_code_3657_, 2);
v_params_3671_ = lean_ctor_get(v_decl_3669_, 2);
lean_inc_ref(v_params_3671_);
v_type_3672_ = lean_ctor_get(v_decl_3669_, 3);
lean_inc_ref(v_type_3672_);
v_value_3673_ = lean_ctor_get(v_decl_3669_, 4);
lean_inc_ref(v_value_3673_);
v___x_3674_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3674_, 0, v_value_3673_);
v___x_3675_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3674_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3696_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3696_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3696_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
uint8_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = 0;
v___x_3681_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3680_, v_decl_3669_, v_type_3672_, v_params_3671_, v_a_3676_, v_a_3660_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3681_, 1);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 1);
lean_ctor_set(v___x_3678_, 0, v_a_3682_);
v___x_3684_ = v___x_3678_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3682_);
v___x_3684_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3685_, 0, v_k_3670_);
v___x_3686_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3684_, v___x_3685_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
return v___x_3686_;
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_del_object(v___x_3678_);
lean_dec_ref(v_k_3670_);
v_a_3688_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3681_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3681_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3672_);
lean_dec_ref(v_params_3671_);
lean_dec_ref(v_k_3670_);
lean_dec_ref(v_decl_3669_);
return v___x_3675_;
}
}
case 2:
{
lean_object* v_decl_3697_; lean_object* v_k_3698_; lean_object* v_params_3699_; lean_object* v_type_3700_; lean_object* v_value_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_decl_3697_ = lean_ctor_get(v_code_3657_, 0);
lean_inc_ref(v_decl_3697_);
v_k_3698_ = lean_ctor_get(v_code_3657_, 1);
lean_inc_ref(v_k_3698_);
lean_dec_ref_known(v_code_3657_, 2);
v_params_3699_ = lean_ctor_get(v_decl_3697_, 2);
lean_inc_ref(v_params_3699_);
v_type_3700_ = lean_ctor_get(v_decl_3697_, 3);
lean_inc_ref(v_type_3700_);
v_value_3701_ = lean_ctor_get(v_decl_3697_, 4);
lean_inc_ref(v_value_3701_);
v___x_3702_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3702_, 0, v_value_3701_);
v___x_3703_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3702_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3724_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3724_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3724_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
uint8_t v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = 0;
v___x_3709_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3708_, v_decl_3697_, v_type_3700_, v_params_3699_, v_a_3704_, v_a_3660_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 2);
lean_ctor_set(v___x_3706_, 0, v_a_3710_);
v___x_3712_ = v___x_3706_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3710_);
v___x_3712_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3713_, 0, v_k_3698_);
v___x_3714_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3712_, v___x_3713_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
return v___x_3714_;
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_del_object(v___x_3706_);
lean_dec_ref(v_k_3698_);
v_a_3716_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3709_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3709_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3700_);
lean_dec_ref(v_params_3699_);
lean_dec_ref(v_k_3698_);
lean_dec_ref(v_decl_3697_);
return v___x_3703_;
}
}
case 4:
{
lean_object* v_cases_3725_; lean_object* v___x_3726_; 
v_cases_3725_ = lean_ctor_get(v_code_3657_, 0);
lean_inc_ref_n(v_cases_3725_, 2);
v___x_3726_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3725_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v___x_3728_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3725_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_a_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_st_mk_ref(v___x_3729_);
v___x_3731_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3730_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v___x_3732_; lean_object* v_typeName_3733_; lean_object* v_resultType_3734_; lean_object* v_discr_3735_; lean_object* v_alts_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref_known(v___x_3731_, 1);
v___x_3732_ = lean_st_ref_get(v___x_3730_);
lean_dec(v___x_3730_);
v_typeName_3733_ = lean_ctor_get(v_cases_3725_, 0);
v_resultType_3734_ = lean_ctor_get(v_cases_3725_, 1);
v_discr_3735_ = lean_ctor_get(v_cases_3725_, 2);
v_alts_3736_ = lean_ctor_get(v_cases_3725_, 3);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_cases_3725_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3738_ = v_cases_3725_;
v_isShared_3739_ = v_isSharedCheck_3779_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_alts_3736_);
lean_inc(v_discr_3735_);
lean_inc(v_resultType_3734_);
lean_inc(v_typeName_3733_);
lean_dec(v_cases_3725_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3779_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v_newArms_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_newArms_3740_ = lean_ctor_get(v___x_3732_, 1);
lean_inc_ref(v_newArms_3740_);
lean_dec(v___x_3732_);
v___x_3741_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3736_);
v___x_3742_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3740_, v___x_3741_, v_alts_3736_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3770_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3770_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3770_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
uint8_t v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___y_3751_; uint8_t v___y_3763_; size_t v___x_3765_; size_t v___x_3766_; uint8_t v___x_3767_; 
v___x_3747_ = 0;
v___x_3748_ = lean_box(2);
v___x_3749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3740_, v___x_3748_);
lean_dec_ref(v_newArms_3740_);
v___x_3765_ = lean_ptr_addr(v_alts_3736_);
lean_dec_ref(v_alts_3736_);
v___x_3766_ = lean_ptr_addr(v_a_3743_);
v___x_3767_ = lean_usize_dec_eq(v___x_3765_, v___x_3766_);
if (v___x_3767_ == 0)
{
v___y_3763_ = v___x_3767_;
goto v___jp_3762_;
}
else
{
size_t v___x_3768_; uint8_t v___x_3769_; 
v___x_3768_ = lean_ptr_addr(v_resultType_3734_);
v___x_3769_ = lean_usize_dec_eq(v___x_3768_, v___x_3768_);
v___y_3763_ = v___x_3769_;
goto v___jp_3762_;
}
v___jp_3750_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3752_ = lean_array_mk(v___x_3749_);
v___x_3753_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3747_, v___x_3752_, v___y_3751_);
lean_dec_ref(v___x_3752_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3753_);
v___x_3755_ = v___x_3745_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
v___jp_3757_:
{
lean_object* v___x_3759_; 
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 3, v_a_3743_);
v___x_3759_ = v___x_3738_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_typeName_3733_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_resultType_3734_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_discr_3735_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_a_3743_);
v___x_3759_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
v___y_3751_ = v___x_3760_;
goto v___jp_3750_;
}
}
v___jp_3762_:
{
if (v___y_3763_ == 0)
{
lean_dec_ref_known(v_code_3657_, 1);
goto v___jp_3757_;
}
else
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Lean_instBEqFVarId_beq(v_discr_3735_, v_discr_3735_);
if (v___x_3764_ == 0)
{
lean_dec_ref_known(v_code_3657_, 1);
goto v___jp_3757_;
}
else
{
lean_dec(v_a_3743_);
lean_del_object(v___x_3738_);
lean_dec(v_discr_3735_);
lean_dec_ref(v_resultType_3734_);
lean_dec(v_typeName_3733_);
v___y_3751_ = v_code_3657_;
goto v___jp_3750_;
}
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v_newArms_3740_);
lean_del_object(v___x_3738_);
lean_dec_ref(v_alts_3736_);
lean_dec(v_discr_3735_);
lean_dec_ref(v_resultType_3734_);
lean_dec(v_typeName_3733_);
lean_dec_ref_known(v_code_3657_, 1);
v_a_3771_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3742_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3742_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v___x_3730_);
lean_dec_ref_known(v_code_3657_, 1);
lean_dec_ref(v_cases_3725_);
v_a_3780_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3731_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3731_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref_known(v_code_3657_, 1);
lean_dec_ref(v_cases_3725_);
v_a_3788_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3726_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3726_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
default: 
{
uint8_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3796_ = 0;
lean_inc(v_a_3658_);
v___x_3797_ = lean_array_mk(v_a_3658_);
v___x_3798_ = l_Array_reverse___redArg(v___x_3797_);
v___x_3799_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3796_, v___x_3798_, v_code_3657_);
lean_dec_ref(v___x_3798_);
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
return v___x_3800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3809_, lean_object* v_i_3810_, lean_object* v_as_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3818_ = lean_array_get_size(v_as_3811_);
v___x_3819_ = lean_nat_dec_lt(v_i_3810_, v___x_3818_);
if (v___x_3819_ == 0)
{
lean_object* v___x_3820_; 
lean_dec(v_i_3810_);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v_as_3811_);
return v___x_3820_;
}
else
{
lean_object* v_options_3821_; lean_object* v_inheritedTraceOptions_3822_; uint8_t v_hasTrace_3823_; uint8_t v___x_3824_; lean_object* v_a_3825_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; 
v_options_3821_ = lean_ctor_get(v___y_3815_, 2);
v_inheritedTraceOptions_3822_ = lean_ctor_get(v___y_3815_, 13);
v_hasTrace_3823_ = lean_ctor_get_uint8(v_options_3821_, sizeof(void*)*1);
v___x_3824_ = 0;
v_a_3825_ = lean_array_fget_borrowed(v_as_3811_, v_i_3810_);
v___x_3856_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3825_);
v___x_3857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3809_, v___x_3856_);
if (v_hasTrace_3823_ == 0)
{
lean_dec(v___x_3856_);
v___y_3859_ = v___y_3813_;
v___y_3860_ = v___y_3814_;
v___y_3861_ = v___y_3815_;
v___y_3862_ = v___y_3816_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3867_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3868_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3822_, v_options_3821_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_dec(v___x_3856_);
v___y_3859_ = v___y_3813_;
v___y_3860_ = v___y_3814_;
v___y_3861_ = v___y_3815_;
v___y_3862_ = v___y_3816_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3870_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3871_ = lean_unsigned_to_nat(0u);
v___x_3872_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3856_, v___x_3871_);
v___x_3873_ = l_Lean_MessageData_ofFormat(v___x_3872_);
v___x_3874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3870_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3874_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v___x_3877_ = l_List_lengthTR___redArg(v___x_3857_);
v___x_3878_ = l_Nat_reprFast(v___x_3877_);
v___x_3879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
v___x_3880_ = l_Lean_MessageData_ofFormat(v___x_3879_);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3876_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3867_, v___x_3881_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_dec_ref_known(v___x_3882_, 1);
v___y_3859_ = v___y_3813_;
v___y_3860_ = v___y_3814_;
v___y_3861_ = v___y_3815_;
v___y_3862_ = v___y_3816_;
goto v___jp_3858_;
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v___x_3857_);
lean_dec_ref(v_as_3811_);
lean_dec(v_i_3810_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
v___jp_3826_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3833_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3824_, v___y_3831_, v___y_3832_);
lean_dec_ref(v___y_3831_);
v___x_3834_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3834_, 0, v___x_3833_);
v___x_3835_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3834_, v___y_3830_, v___y_3827_, v___y_3828_, v___y_3829_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; size_t v___x_3838_; size_t v___x_3839_; uint8_t v___x_3840_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
lean_inc(v_a_3825_);
v___x_3837_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3825_, v_a_3836_);
v___x_3838_ = lean_ptr_addr(v_a_3825_);
v___x_3839_ = lean_ptr_addr(v___x_3837_);
v___x_3840_ = lean_usize_dec_eq(v___x_3838_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = lean_unsigned_to_nat(1u);
v___x_3842_ = lean_nat_add(v_i_3810_, v___x_3841_);
v___x_3843_ = lean_array_fset(v_as_3811_, v_i_3810_, v___x_3837_);
lean_dec(v_i_3810_);
v_i_3810_ = v___x_3842_;
v_as_3811_ = v___x_3843_;
goto _start;
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec_ref(v___x_3837_);
v___x_3845_ = lean_unsigned_to_nat(1u);
v___x_3846_ = lean_nat_add(v_i_3810_, v___x_3845_);
lean_dec(v_i_3810_);
v_i_3810_ = v___x_3846_;
goto _start;
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref(v_as_3811_);
lean_dec(v_i_3810_);
v_a_3848_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3835_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3835_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
v___jp_3858_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_array_mk(v___x_3857_);
switch(lean_obj_tag(v_a_3825_))
{
case 0:
{
lean_object* v_code_3864_; 
v_code_3864_ = lean_ctor_get(v_a_3825_, 2);
lean_inc_ref(v_code_3864_);
v___y_3827_ = v___y_3860_;
v___y_3828_ = v___y_3861_;
v___y_3829_ = v___y_3862_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3863_;
v___y_3832_ = v_code_3864_;
goto v___jp_3826_;
}
case 1:
{
lean_object* v_code_3865_; 
v_code_3865_ = lean_ctor_get(v_a_3825_, 1);
lean_inc_ref(v_code_3865_);
v___y_3827_ = v___y_3860_;
v___y_3828_ = v___y_3861_;
v___y_3829_ = v___y_3862_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3863_;
v___y_3832_ = v_code_3865_;
goto v___jp_3826_;
}
default: 
{
lean_object* v_code_3866_; 
v_code_3866_ = lean_ctor_get(v_a_3825_, 0);
lean_inc_ref(v_code_3866_);
v___y_3827_ = v___y_3860_;
v___y_3828_ = v___y_3861_;
v___y_3829_ = v___y_3862_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3863_;
v___y_3832_ = v_code_3866_;
goto v___jp_3826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3891_, lean_object* v_i_3892_, lean_object* v_as_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3891_, v_i_3892_, v_as_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___x_3891_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3901_, lean_object* v_v_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
if (lean_obj_tag(v_v_3902_) == 0)
{
lean_object* v_code_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3933_; 
v_code_3909_ = lean_ctor_get(v_v_3902_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_v_3902_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3911_ = v_v_3902_;
v_isShared_3912_ = v_isSharedCheck_3933_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_code_3909_);
lean_dec(v_v_3902_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3933_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3913_; 
lean_inc(v___y_3907_);
lean_inc_ref(v___y_3906_);
lean_inc(v___y_3905_);
lean_inc_ref(v___y_3904_);
lean_inc(v___y_3903_);
v___x_3913_ = lean_apply_7(v_f_3901_, v_code_3909_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, lean_box(0));
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v_a_3914_);
v___x_3919_ = v___x_3911_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3919_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_del_object(v___x_3911_);
v_a_3925_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3913_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3913_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v___x_3934_; 
lean_dec_ref(v_f_3901_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_v_3902_);
return v___x_3934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3935_, lean_object* v_v_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3935_, v_v_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3944_, lean_object* v_f_3945_, lean_object* v_v_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3945_, v_v_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3954_, lean_object* v_f_3955_, lean_object* v_v_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint8_t v_pu_boxed_3963_; lean_object* v_res_3964_; 
v_pu_boxed_3963_ = lean_unbox(v_pu_3954_);
v_res_3964_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_3963_, v_f_3955_, v_v_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_toSignature_3972_; lean_object* v_value_3973_; uint8_t v_recursive_3974_; lean_object* v_inlineAttr_x3f_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4001_; 
v_toSignature_3972_ = lean_ctor_get(v_decl_3966_, 0);
v_value_3973_ = lean_ctor_get(v_decl_3966_, 1);
v_recursive_3974_ = lean_ctor_get_uint8(v_decl_3966_, sizeof(void*)*3);
v_inlineAttr_x3f_3975_ = lean_ctor_get(v_decl_3966_, 2);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_decl_3966_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3977_ = v_decl_3966_;
v_isShared_3978_ = v_isSharedCheck_4001_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_inlineAttr_x3f_3975_);
lean_inc(v_value_3973_);
lean_inc(v_toSignature_3972_);
lean_dec(v_decl_3966_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4001_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_3980_ = lean_box(0);
v___x_3981_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_3979_, v_value_3973_, v___x_3980_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3992_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_3992_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3992_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v_a_3982_);
v___x_3987_ = v___x_3977_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_toSignature_3972_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_a_3982_);
lean_ctor_set(v_reuseFailAlloc_3991_, 2, v_inlineAttr_x3f_3975_);
lean_ctor_set_uint8(v_reuseFailAlloc_3991_, sizeof(void*)*3, v_recursive_3974_);
v___x_3987_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3987_);
v___x_3989_ = v___x_3984_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_del_object(v___x_3977_);
lean_dec(v_inlineAttr_x3f_3975_);
lean_dec_ref(v_toSignature_3972_);
v_a_3993_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3981_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3981_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_4025_, lean_object* v___f_4026_, lean_object* v_occurrence_4027_, lean_object* v_h_4028_){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_4030_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_4029_, v_phase_4025_, v___f_4026_, v_occurrence_4027_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_4031_, lean_object* v___f_4032_, lean_object* v_occurrence_4033_, lean_object* v_h_4034_){
_start:
{
uint8_t v_phase_boxed_4035_; lean_object* v_res_4036_; 
v_phase_boxed_4035_ = lean_unbox(v_phase_4031_);
v_res_4036_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_4035_, v___f_4032_, v_occurrence_4033_, v_h_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_4038_, lean_object* v_occurrence_4039_){
_start:
{
lean_object* v___f_4040_; lean_object* v___x_4041_; lean_object* v___f_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; 
v___f_4040_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_4041_ = lean_box(v_phase_4038_);
v___f_4042_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4042_, 0, v___x_4041_);
lean_closure_set(v___f_4042_, 1, v___f_4040_);
lean_closure_set(v___f_4042_, 2, v_occurrence_4039_);
v___x_4043_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_4044_ = 0;
v___x_4045_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_4043_, v_phase_4038_, v___x_4044_, v___f_4042_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_4046_, lean_object* v_occurrence_4047_){
_start:
{
uint8_t v_phase_boxed_4048_; lean_object* v_res_4049_; 
v_phase_boxed_4048_ = lean_unbox(v_phase_4046_);
v_res_4049_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_4048_, v_occurrence_4047_);
return v_res_4049_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = lean_unsigned_to_nat(3411573818u);
v___x_4102_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4103_ = l_Lean_Name_num___override(v___x_4102_, v___x_4101_);
return v___x_4103_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4105_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4106_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4107_ = l_Lean_Name_str___override(v___x_4106_, v___x_4105_);
return v___x_4107_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4110_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4111_ = l_Lean_Name_str___override(v___x_4110_, v___x_4109_);
return v___x_4111_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = lean_unsigned_to_nat(2u);
v___x_4113_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4114_ = l_Lean_Name_num___override(v___x_4113_, v___x_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4116_; uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4116_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4117_ = 1;
v___x_4118_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4119_ = l_Lean_registerTraceClass(v___x_4116_, v___x_4117_, v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4121_;
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
