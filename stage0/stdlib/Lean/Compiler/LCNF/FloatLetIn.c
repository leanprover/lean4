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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_array_mk(lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "EST"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Out"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 80, 83, 99, 239, 159, 42, 46)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 22, 165, 44, 41, 63, 187, 255)}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ST"};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__5_value),LEAN_SCALAR_PTR_LITERAL(251, 141, 99, 66, 199, 185, 233, 139)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 82, 234, 1, 110, 68, 195, 153)}};
static const lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_nbuckets_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_410_ = lean_array_get_size(v_data_409_);
v___x_411_ = lean_unsigned_to_nat(2u);
v_nbuckets_412_ = lean_nat_mul(v___x_410_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_box(0);
v___x_415_ = lean_mk_array(v_nbuckets_412_, v___x_414_);
v___x_416_ = lean_array_propagate_mark(v_data_409_, v___x_415_);
v___x_417_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v___x_413_, v_data_409_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object* v_m_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v_size_421_; lean_object* v_buckets_422_; lean_object* v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_bkt_436_; uint8_t v___x_437_; 
v_size_421_ = lean_ctor_get(v_m_418_, 0);
v_buckets_422_ = lean_ctor_get(v_m_418_, 1);
v___x_423_ = lean_array_get_size(v_buckets_422_);
v___x_424_ = l_Lean_instHashableFVarId_hash(v_a_419_);
v___x_425_ = 32ULL;
v___x_426_ = lean_uint64_shift_right(v___x_424_, v___x_425_);
v_fold_427_ = lean_uint64_xor(v___x_424_, v___x_426_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_423_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v_bkt_436_ = lean_array_uget_borrowed(v_buckets_422_, v___x_435_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_419_, v_bkt_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_458_; 
lean_inc_ref(v_buckets_422_);
lean_inc(v_size_421_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_m_418_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_459_ = lean_ctor_get(v_m_418_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_m_418_, 0);
lean_dec(v_unused_460_);
v___x_439_ = v_m_418_;
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_m_418_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_size_x27_442_; lean_object* v___x_443_; lean_object* v_buckets_x27_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v_size_x27_442_ = lean_nat_add(v_size_421_, v___x_441_);
lean_dec(v_size_421_);
lean_inc(v_bkt_436_);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v_a_419_);
lean_ctor_set(v___x_443_, 1, v_b_420_);
lean_ctor_set(v___x_443_, 2, v_bkt_436_);
v_buckets_x27_444_ = lean_array_uset(v_buckets_422_, v___x_435_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(4u);
v___x_446_ = lean_nat_mul(v_size_x27_442_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(3u);
v___x_448_ = lean_nat_div(v___x_446_, v___x_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_array_get_size(v_buckets_x27_444_);
v___x_450_ = lean_nat_dec_le(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v_val_451_; lean_object* v___x_453_; 
v_val_451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_444_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_val_451_);
lean_ctor_set(v___x_439_, 0, v_size_x27_442_);
v___x_453_ = v___x_439_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_val_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_456_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_buckets_x27_444_);
lean_ctor_set(v___x_439_, 0, v_size_x27_442_);
v___x_456_ = v___x_439_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_size_x27_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_buckets_x27_444_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_dec(v_b_420_);
lean_dec(v_a_419_);
return v_m_418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object* v_var_461_, uint8_t v_borrowed_462_, lean_object* v_a_463_){
_start:
{
if (lean_obj_tag(v_var_461_) == 1)
{
lean_object* v_fvarId_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_483_; 
v_fvarId_465_ = lean_ctor_get(v_var_461_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_var_461_);
if (v_isSharedCheck_483_ == 0)
{
v___x_467_ = v_var_461_;
v_isShared_468_ = v_isSharedCheck_483_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_fvarId_465_);
lean_dec(v_var_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_483_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_st_ref_get(v_a_463_);
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_469_, v_fvarId_465_);
lean_dec(v___x_469_);
if (v_borrowed_462_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_471_ = lean_st_ref_take(v_a_463_);
v___x_472_ = lean_box(0);
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_471_, v_fvarId_465_, v___x_472_);
v___x_474_ = lean_st_ref_put(v_a_463_, v___x_473_);
v___x_475_ = lean_box(v___x_470_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 0);
lean_ctor_set(v___x_467_, 0, v___x_475_);
v___x_477_ = v___x_467_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_fvarId_465_);
v___x_479_ = lean_box(v___x_470_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 0);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_481_ = v___x_467_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_var_461_);
v___x_484_ = 0;
v___x_485_ = lean_box(v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object* v_var_487_, lean_object* v_borrowed_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
uint8_t v_borrowed_boxed_491_; lean_object* v_res_492_; 
v_borrowed_boxed_491_ = lean_unbox(v_borrowed_488_);
v_res_492_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_487_, v_borrowed_boxed_491_, v_a_489_);
lean_dec(v_a_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object* v_var_493_, uint8_t v_borrowed_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_493_, v_borrowed_494_, v_a_495_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object* v_var_502_, lean_object* v_borrowed_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
uint8_t v_borrowed_boxed_510_; lean_object* v_res_511_; 
v_borrowed_boxed_510_ = lean_unbox(v_borrowed_503_);
v_res_511_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_502_, v_borrowed_boxed_510_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
return v_res_511_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_m_513_, lean_object* v_a_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_513_, v_a_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object* v_00_u03b2_516_, lean_object* v_m_517_, lean_object* v_a_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_516_, v_m_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_m_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_522_, v_a_523_, v_b_524_);
return v___x_525_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_530_, lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_530_, v_a_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_a_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object* v_00_u03b2_535_, lean_object* v_data_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_data_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_538_, lean_object* v_i_539_, lean_object* v_source_540_, lean_object* v_target_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v_i_539_, v_source_540_, v_target_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_x_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object* v_as_547_, size_t v_i_548_, size_t v_stop_549_, uint8_t v_b_550_, lean_object* v___y_551_){
_start:
{
uint8_t v_a_554_; lean_object* v___y_559_; uint8_t v___x_562_; 
v___x_562_ = lean_usize_dec_eq(v_i_548_, v_stop_549_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_array_uget_borrowed(v_as_547_, v_i_548_);
lean_inc(v___x_563_);
v___x_564_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_563_, v___x_562_, v___y_551_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; uint8_t v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
v___x_566_ = lean_unbox(v_a_565_);
lean_dec(v_a_565_);
if (v___x_566_ == 0)
{
lean_dec_ref_known(v___x_564_, 1);
v_a_554_ = v_b_550_;
goto v___jp_553_;
}
else
{
v___y_559_ = v___x_564_;
goto v___jp_558_;
}
}
else
{
v___y_559_ = v___x_564_;
goto v___jp_558_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_box(v_b_550_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
v___jp_553_:
{
size_t v___x_555_; size_t v___x_556_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_548_, v___x_555_);
v_i_548_ = v___x_556_;
v_b_550_ = v_a_554_;
goto _start;
}
v___jp_558_:
{
if (lean_obj_tag(v___y_559_) == 0)
{
lean_object* v_a_560_; uint8_t v___x_561_; 
v_a_560_ = lean_ctor_get(v___y_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___y_559_, 1);
v___x_561_ = lean_unbox(v_a_560_);
lean_dec(v_a_560_);
v_a_554_ = v___x_561_;
goto v___jp_553_;
}
else
{
return v___y_559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_569_, lean_object* v_i_570_, lean_object* v_stop_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
size_t v_i_boxed_575_; size_t v_stop_boxed_576_; uint8_t v_b_boxed_577_; lean_object* v_res_578_; 
v_i_boxed_575_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_stop_boxed_576_ = lean_unbox_usize(v_stop_571_);
lean_dec(v_stop_571_);
v_b_boxed_577_ = lean_unbox(v_b_572_);
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_569_, v_i_boxed_575_, v_stop_boxed_576_, v_b_boxed_577_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v_as_569_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_579_, lean_object* v_args_580_, lean_object* v_val_581_, lean_object* v_a_582_, uint8_t v_b_583_, lean_object* v___y_584_){
_start:
{
uint8_t v_a_587_; uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_lt(v_a_582_, v_upperBound_579_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_a_582_);
v___x_592_ = lean_box(v_b_583_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v_params_594_; lean_object* v___x_595_; uint8_t v___y_597_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_params_594_ = lean_ctor_get(v_val_581_, 3);
v___x_595_ = lean_array_fget_borrowed(v_args_580_, v_a_582_);
v___x_601_ = lean_array_get_size(v_params_594_);
v___x_602_ = lean_nat_dec_lt(v_a_582_, v___x_601_);
if (v___x_602_ == 0)
{
v___y_597_ = v___x_602_;
goto v___jp_596_;
}
else
{
lean_object* v___x_603_; uint8_t v_borrow_604_; 
v___x_603_ = lean_array_fget_borrowed(v_params_594_, v_a_582_);
v_borrow_604_ = lean_ctor_get_uint8(v___x_603_, sizeof(void*)*3);
v___y_597_ = v_borrow_604_;
goto v___jp_596_;
}
v___jp_596_:
{
lean_object* v___x_598_; 
lean_inc(v___x_595_);
v___x_598_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_595_, v___y_597_, v___y_584_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; uint8_t v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_600_ == 0)
{
v_a_587_ = v_b_583_;
goto v___jp_586_;
}
else
{
v_a_587_ = v___x_591_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_a_582_);
return v___x_598_;
}
}
}
v___jp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_a_582_, v___x_588_);
lean_dec(v_a_582_);
v_a_582_ = v___x_589_;
v_b_583_ = v_a_587_;
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
v___x_985_ = lean_st_ref_put(v_a_975_, v___x_984_);
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
v___x_994_ = lean_st_ref_put(v_a_975_, v___x_993_);
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
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_8045__overap_1148_; lean_object* v___x_1149_; 
v___x_1144_ = l_ReaderT_instMonad___redArg(v___x_1143_);
v___x_1145_ = l_StateRefT_x27_instMonad___redArg(v___x_1144_);
v___x_1146_ = lean_box(0);
v___x_1147_ = l_instInhabitedOfMonad___redArg(v___x_1145_, v___x_1146_);
v___x_8045__overap_1148_ = lean_panic_fn_borrowed(v___x_1147_, v_msg_1087_);
lean_dec(v___x_1147_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1089_);
lean_inc(v___y_1088_);
v___x_1149_ = lean_apply_7(v___x_8045__overap_1148_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, lean_box(0));
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
lean_object* v_struct_1367_; lean_object* v___x_1368_; 
v_struct_1367_ = lean_ctor_get(v_e_1349_, 2);
lean_inc(v_struct_1367_);
lean_dec_ref_known(v_e_1349_, 3);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1368_ = lean_apply_8(v_f_1348_, v_struct_1367_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1368_;
}
case 3:
{
lean_object* v_args_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_args_1369_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_args_1369_);
lean_dec_ref_known(v_e_1349_, 3);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_array_get_size(v_args_1369_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_nat_dec_lt(v___x_1370_, v___x_1371_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref(v_args_1369_);
lean_dec_ref(v_f_1348_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
return v___x_1374_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1371_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1369_, v___x_1375_, v___x_1376_, v___x_1372_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1369_);
return v___x_1377_;
}
}
case 4:
{
lean_object* v_fvarId_1378_; lean_object* v_args_1379_; lean_object* v___x_1380_; 
v_fvarId_1378_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_fvarId_1378_);
v_args_1379_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1379_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc_ref(v_f_1348_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1380_ = lean_apply_8(v_f_1348_, v_fvarId_1378_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1380_, 0);
lean_dec(v_unused_1395_);
v___x_1382_ = v___x_1380_;
v_isShared_1383_ = v_isSharedCheck_1394_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v___x_1380_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1394_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_array_get_size(v_args_1379_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_nat_dec_lt(v___x_1384_, v___x_1385_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref(v_args_1379_);
lean_dec_ref(v_f_1348_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1386_);
v___x_1389_ = v___x_1382_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1386_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
lean_del_object(v___x_1382_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = lean_usize_of_nat(v___x_1385_);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1379_, v___x_1391_, v___x_1392_, v___x_1386_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1379_);
return v___x_1393_;
}
}
}
else
{
lean_dec_ref(v_args_1379_);
lean_dec_ref(v_f_1348_);
return v___x_1380_;
}
}
case 5:
{
lean_object* v_args_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_args_1396_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1396_);
lean_dec_ref_known(v_e_1349_, 2);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_array_get_size(v_args_1396_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_nat_dec_lt(v___x_1397_, v___x_1398_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec_ref(v_args_1396_);
lean_dec_ref(v_f_1348_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
return v___x_1401_;
}
else
{
size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = lean_usize_of_nat(v___x_1398_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1396_, v___x_1402_, v___x_1403_, v___x_1399_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1396_);
return v___x_1404_;
}
}
case 6:
{
lean_object* v_var_1405_; lean_object* v___x_1406_; 
v_var_1405_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_var_1405_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1406_ = lean_apply_8(v_f_1348_, v_var_1405_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1406_;
}
case 7:
{
lean_object* v_var_1407_; lean_object* v___x_1408_; 
v_var_1407_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_var_1407_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1408_ = lean_apply_8(v_f_1348_, v_var_1407_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1408_;
}
case 8:
{
lean_object* v_var_1409_; lean_object* v___x_1410_; 
v_var_1409_ = lean_ctor_get(v_e_1349_, 2);
lean_inc(v_var_1409_);
lean_dec_ref_known(v_e_1349_, 3);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1410_ = lean_apply_8(v_f_1348_, v_var_1409_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1410_;
}
case 9:
{
lean_object* v_args_1411_; 
v_args_1411_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1411_);
lean_dec_ref_known(v_e_1349_, 2);
v_args_1358_ = v_args_1411_;
goto v___jp_1357_;
}
case 10:
{
lean_object* v_args_1412_; 
v_args_1412_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_args_1412_);
lean_dec_ref_known(v_e_1349_, 2);
v_args_1358_ = v_args_1412_;
goto v___jp_1357_;
}
case 11:
{
lean_object* v_var_1413_; lean_object* v___x_1414_; 
v_var_1413_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_var_1413_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1414_ = lean_apply_8(v_f_1348_, v_var_1413_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1414_;
}
case 12:
{
lean_object* v_var_1415_; lean_object* v_args_1416_; lean_object* v___x_1417_; 
v_var_1415_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_var_1415_);
v_args_1416_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_args_1416_);
lean_dec_ref_known(v_e_1349_, 3);
lean_inc_ref(v_f_1348_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1417_ = lean_apply_8(v_f_1348_, v_var_1415_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1417_, 0);
lean_dec(v_unused_1432_);
v___x_1419_ = v___x_1417_;
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v___x_1417_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_array_get_size(v_args_1416_);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_nat_dec_lt(v___x_1421_, v___x_1422_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_args_1416_);
lean_dec_ref(v_f_1348_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1423_);
v___x_1426_ = v___x_1419_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1423_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
lean_del_object(v___x_1419_);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = lean_usize_of_nat(v___x_1422_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1416_, v___x_1428_, v___x_1429_, v___x_1423_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1416_);
return v___x_1430_;
}
}
}
else
{
lean_dec_ref(v_args_1416_);
lean_dec_ref(v_f_1348_);
return v___x_1417_;
}
}
case 13:
{
lean_object* v_fvarId_1433_; lean_object* v___x_1434_; 
v_fvarId_1433_ = lean_ctor_get(v_e_1349_, 1);
lean_inc(v_fvarId_1433_);
lean_dec_ref_known(v_e_1349_, 2);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1434_ = lean_apply_8(v_f_1348_, v_fvarId_1433_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1434_;
}
case 14:
{
lean_object* v_fvarId_1435_; lean_object* v___x_1436_; 
v_fvarId_1435_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_fvarId_1435_);
lean_dec_ref_known(v_e_1349_, 1);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1436_ = lean_apply_8(v_f_1348_, v_fvarId_1435_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1436_;
}
case 15:
{
lean_object* v_fvarId_1437_; lean_object* v___x_1438_; 
v_fvarId_1437_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_fvarId_1437_);
lean_dec_ref_known(v_e_1349_, 1);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
v___x_1438_ = lean_apply_8(v_f_1348_, v_fvarId_1437_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
return v___x_1438_;
}
default: 
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v_e_1349_);
lean_dec_ref(v_f_1348_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
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
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_of_nat(v___x_1360_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1347_, v_f_1348_, v_args_1358_, v___x_1364_, v___x_1365_, v___x_1361_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_args_1358_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1441_, lean_object* v_f_1442_, lean_object* v_e_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_pu_boxed_1451_; lean_object* v_res_1452_; 
v_pu_boxed_1451_ = lean_unbox(v_pu_1441_);
v_res_1452_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1451_, v_f_1442_, v_e_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec(v___y_1444_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1453_, lean_object* v_f_1454_, lean_object* v_decl_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_type_1463_; lean_object* v_value_1464_; lean_object* v___x_1465_; 
v_type_1463_ = lean_ctor_get(v_decl_1455_, 2);
lean_inc_ref(v_type_1463_);
v_value_1464_ = lean_ctor_get(v_decl_1455_, 3);
lean_inc(v_value_1464_);
lean_dec_ref(v_decl_1455_);
lean_inc_ref(v_f_1454_);
v___x_1465_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1454_, v_type_1463_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; 
lean_dec_ref_known(v___x_1465_, 1);
v___x_1466_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1453_, v_f_1454_, v_value_1464_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1466_;
}
else
{
lean_dec(v_value_1464_);
lean_dec_ref(v_f_1454_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1467_, lean_object* v_f_1468_, lean_object* v_decl_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v_pu_boxed_1477_; lean_object* v_res_1478_; 
v_pu_boxed_1477_ = lean_unbox(v_pu_1467_);
v_res_1478_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1477_, v_f_1468_, v_decl_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1479_, lean_object* v_f_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v_pu_boxed_1489_; lean_object* v_res_1490_; 
v_pu_boxed_1489_ = lean_unbox(v_pu_1479_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1489_, v_f_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1491_, lean_object* v_f_1492_, lean_object* v_as_1493_, size_t v_i_1494_, size_t v_stop_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_eq(v_i_1494_, v_stop_1495_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_box(v_pu_1491_);
lean_inc_ref(v_f_1492_);
v___f_1506_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1506_, 0, v___x_1505_);
lean_closure_set(v___f_1506_, 1, v_f_1492_);
v___x_1507_ = lean_array_uget_borrowed(v_as_1493_, v_i_1494_);
lean_inc(v___x_1507_);
v___x_1508_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1507_, v___f_1506_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; size_t v___x_1510_; size_t v___x_1511_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1494_, v___x_1510_);
v_i_1494_ = v___x_1511_;
v_b_1496_ = v_a_1509_;
goto _start;
}
else
{
lean_dec_ref(v_f_1492_);
return v___x_1508_;
}
}
else
{
lean_object* v___x_1513_; 
lean_dec_ref(v_f_1492_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_b_1496_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1514_, lean_object* v_f_1515_, lean_object* v_c_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
switch(lean_obj_tag(v_c_1516_))
{
case 0:
{
lean_object* v_decl_1524_; lean_object* v_k_1525_; lean_object* v___x_1526_; 
v_decl_1524_ = lean_ctor_get(v_c_1516_, 0);
lean_inc_ref(v_decl_1524_);
v_k_1525_ = lean_ctor_get(v_c_1516_, 1);
lean_inc_ref(v_k_1525_);
lean_dec_ref_known(v_c_1516_, 2);
lean_inc_ref(v_f_1515_);
v___x_1526_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1514_, v_f_1515_, v_decl_1524_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref_known(v___x_1526_, 1);
v_c_1516_ = v_k_1525_;
goto _start;
}
else
{
lean_dec_ref(v_k_1525_);
lean_dec_ref(v_f_1515_);
return v___x_1526_;
}
}
case 3:
{
lean_object* v_fvarId_1528_; lean_object* v_args_1529_; lean_object* v___x_1530_; 
v_fvarId_1528_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1528_);
v_args_1529_ = lean_ctor_get(v_c_1516_, 1);
lean_inc_ref(v_args_1529_);
lean_dec_ref_known(v_c_1516_, 2);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1530_ = lean_apply_8(v_f_1515_, v_fvarId_1528_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1530_, 0);
lean_dec(v_unused_1545_);
v___x_1532_ = v___x_1530_;
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v___x_1530_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_array_get_size(v_args_1529_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_nat_dec_lt(v___x_1534_, v___x_1535_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref(v_args_1529_);
lean_dec_ref(v_f_1515_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1539_ = v___x_1532_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1536_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
lean_del_object(v___x_1532_);
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = lean_usize_of_nat(v___x_1535_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1514_, v_f_1515_, v_args_1529_, v___x_1541_, v___x_1542_, v___x_1536_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v_args_1529_);
return v___x_1543_;
}
}
}
else
{
lean_dec_ref(v_args_1529_);
lean_dec_ref(v_f_1515_);
return v___x_1530_;
}
}
case 4:
{
lean_object* v_cases_1546_; lean_object* v_resultType_1547_; lean_object* v_discr_1548_; lean_object* v_alts_1549_; lean_object* v___x_1550_; 
v_cases_1546_ = lean_ctor_get(v_c_1516_, 0);
lean_inc_ref(v_cases_1546_);
lean_dec_ref_known(v_c_1516_, 1);
v_resultType_1547_ = lean_ctor_get(v_cases_1546_, 1);
lean_inc_ref(v_resultType_1547_);
v_discr_1548_ = lean_ctor_get(v_cases_1546_, 2);
lean_inc(v_discr_1548_);
v_alts_1549_ = lean_ctor_get(v_cases_1546_, 3);
lean_inc_ref(v_alts_1549_);
lean_dec_ref(v_cases_1546_);
lean_inc_ref(v_f_1515_);
v___x_1550_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1515_, v_resultType_1547_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref_known(v___x_1550_, 1);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1551_ = lean_apply_8(v_f_1515_, v_discr_1548_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1566_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1565_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1565_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_alts_1549_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1560_; 
lean_dec_ref(v_alts_1549_);
lean_dec_ref(v_f_1515_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1560_ = v___x_1553_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1557_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
lean_del_object(v___x_1553_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1556_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1514_, v_f_1515_, v_alts_1549_, v___x_1562_, v___x_1563_, v___x_1557_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v_alts_1549_);
return v___x_1564_;
}
}
}
else
{
lean_dec_ref(v_alts_1549_);
lean_dec_ref(v_f_1515_);
return v___x_1551_;
}
}
else
{
lean_dec_ref(v_alts_1549_);
lean_dec(v_discr_1548_);
lean_dec_ref(v_f_1515_);
return v___x_1550_;
}
}
case 5:
{
lean_object* v_fvarId_1567_; lean_object* v___x_1568_; 
v_fvarId_1567_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1567_);
lean_dec_ref_known(v_c_1516_, 1);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1568_ = lean_apply_8(v_f_1515_, v_fvarId_1567_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
return v___x_1568_;
}
case 6:
{
lean_object* v_type_1569_; lean_object* v___x_1570_; 
v_type_1569_ = lean_ctor_get(v_c_1516_, 0);
lean_inc_ref(v_type_1569_);
lean_dec_ref_known(v_c_1516_, 1);
v___x_1570_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1515_, v_type_1569_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1570_;
}
case 7:
{
lean_object* v_fvarId_1571_; lean_object* v_y_1572_; lean_object* v_k_1573_; lean_object* v___x_1574_; 
v_fvarId_1571_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1571_);
v_y_1572_ = lean_ctor_get(v_c_1516_, 2);
lean_inc(v_y_1572_);
v_k_1573_ = lean_ctor_get(v_c_1516_, 3);
lean_inc_ref(v_k_1573_);
lean_dec_ref_known(v_c_1516_, 4);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1574_ = lean_apply_8(v_f_1515_, v_fvarId_1571_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1574_, 1);
lean_inc_ref(v_f_1515_);
v___x_1575_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1515_, v_y_1572_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec_ref_known(v___x_1575_, 1);
v_c_1516_ = v_k_1573_;
goto _start;
}
else
{
lean_dec_ref(v_k_1573_);
lean_dec_ref(v_f_1515_);
return v___x_1575_;
}
}
else
{
lean_dec_ref(v_k_1573_);
lean_dec(v_y_1572_);
lean_dec_ref(v_f_1515_);
return v___x_1574_;
}
}
case 8:
{
lean_object* v_fvarId_1577_; lean_object* v_y_1578_; lean_object* v_k_1579_; lean_object* v___x_1580_; 
v_fvarId_1577_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1577_);
v_y_1578_ = lean_ctor_get(v_c_1516_, 2);
lean_inc(v_y_1578_);
v_k_1579_ = lean_ctor_get(v_c_1516_, 3);
lean_inc_ref(v_k_1579_);
lean_dec_ref_known(v_c_1516_, 4);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1580_ = lean_apply_8(v_f_1515_, v_fvarId_1577_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref_known(v___x_1580_, 1);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1581_ = lean_apply_8(v_f_1515_, v_y_1578_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v_c_1516_ = v_k_1579_;
goto _start;
}
else
{
lean_dec_ref(v_k_1579_);
lean_dec_ref(v_f_1515_);
return v___x_1581_;
}
}
else
{
lean_dec_ref(v_k_1579_);
lean_dec(v_y_1578_);
lean_dec_ref(v_f_1515_);
return v___x_1580_;
}
}
case 9:
{
lean_object* v_fvarId_1583_; lean_object* v_y_1584_; lean_object* v_ty_1585_; lean_object* v_k_1586_; lean_object* v___x_1587_; 
v_fvarId_1583_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1583_);
v_y_1584_ = lean_ctor_get(v_c_1516_, 3);
lean_inc(v_y_1584_);
v_ty_1585_ = lean_ctor_get(v_c_1516_, 4);
lean_inc_ref(v_ty_1585_);
v_k_1586_ = lean_ctor_get(v_c_1516_, 5);
lean_inc_ref(v_k_1586_);
lean_dec_ref_known(v_c_1516_, 6);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1587_ = lean_apply_8(v_f_1515_, v_fvarId_1583_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref_known(v___x_1587_, 1);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1588_ = lean_apply_8(v_f_1515_, v_y_1584_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; 
lean_dec_ref_known(v___x_1588_, 1);
lean_inc_ref(v_f_1515_);
v___x_1589_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1515_, v_ty_1585_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_dec_ref_known(v___x_1589_, 1);
v_c_1516_ = v_k_1586_;
goto _start;
}
else
{
lean_dec_ref(v_k_1586_);
lean_dec_ref(v_f_1515_);
return v___x_1589_;
}
}
else
{
lean_dec_ref(v_k_1586_);
lean_dec_ref(v_ty_1585_);
lean_dec_ref(v_f_1515_);
return v___x_1588_;
}
}
else
{
lean_dec_ref(v_k_1586_);
lean_dec_ref(v_ty_1585_);
lean_dec(v_y_1584_);
lean_dec_ref(v_f_1515_);
return v___x_1587_;
}
}
case 10:
{
lean_object* v_fvarId_1591_; lean_object* v_k_1592_; lean_object* v___x_1593_; 
v_fvarId_1591_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1591_);
v_k_1592_ = lean_ctor_get(v_c_1516_, 2);
lean_inc_ref(v_k_1592_);
lean_dec_ref_known(v_c_1516_, 3);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1593_ = lean_apply_8(v_f_1515_, v_fvarId_1591_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_dec_ref_known(v___x_1593_, 1);
v_c_1516_ = v_k_1592_;
goto _start;
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1515_);
return v___x_1593_;
}
}
case 11:
{
lean_object* v_fvarId_1595_; lean_object* v_k_1596_; lean_object* v___x_1597_; 
v_fvarId_1595_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1595_);
v_k_1596_ = lean_ctor_get(v_c_1516_, 2);
lean_inc_ref(v_k_1596_);
lean_dec_ref_known(v_c_1516_, 3);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1597_ = lean_apply_8(v_f_1515_, v_fvarId_1595_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref_known(v___x_1597_, 1);
v_c_1516_ = v_k_1596_;
goto _start;
}
else
{
lean_dec_ref(v_k_1596_);
lean_dec_ref(v_f_1515_);
return v___x_1597_;
}
}
case 12:
{
lean_object* v_fvarId_1599_; lean_object* v_k_1600_; lean_object* v___x_1601_; 
v_fvarId_1599_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1599_);
v_k_1600_ = lean_ctor_get(v_c_1516_, 3);
lean_inc_ref(v_k_1600_);
lean_dec_ref_known(v_c_1516_, 4);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1601_ = lean_apply_8(v_f_1515_, v_fvarId_1599_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
v_c_1516_ = v_k_1600_;
goto _start;
}
else
{
lean_dec_ref(v_k_1600_);
lean_dec_ref(v_f_1515_);
return v___x_1601_;
}
}
case 13:
{
lean_object* v_fvarId_1603_; lean_object* v_k_1604_; lean_object* v___x_1605_; 
v_fvarId_1603_ = lean_ctor_get(v_c_1516_, 0);
lean_inc(v_fvarId_1603_);
v_k_1604_ = lean_ctor_get(v_c_1516_, 1);
lean_inc_ref(v_k_1604_);
lean_dec_ref_known(v_c_1516_, 2);
lean_inc_ref(v_f_1515_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
v___x_1605_ = lean_apply_8(v_f_1515_, v_fvarId_1603_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_dec_ref_known(v___x_1605_, 1);
v_c_1516_ = v_k_1604_;
goto _start;
}
else
{
lean_dec_ref(v_k_1604_);
lean_dec_ref(v_f_1515_);
return v___x_1605_;
}
}
default: 
{
lean_object* v_decl_1607_; lean_object* v_k_1608_; lean_object* v_params_1609_; lean_object* v_type_1610_; lean_object* v_value_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_decl_1607_ = lean_ctor_get(v_c_1516_, 0);
lean_inc_ref(v_decl_1607_);
v_k_1608_ = lean_ctor_get(v_c_1516_, 1);
lean_inc_ref(v_k_1608_);
lean_dec_ref(v_c_1516_);
v_params_1609_ = lean_ctor_get(v_decl_1607_, 2);
lean_inc_ref(v_params_1609_);
v_type_1610_ = lean_ctor_get(v_decl_1607_, 3);
lean_inc_ref(v_type_1610_);
v_value_1611_ = lean_ctor_get(v_decl_1607_, 4);
lean_inc_ref(v_value_1611_);
lean_dec_ref(v_decl_1607_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_array_get_size(v_params_1609_);
v___x_1614_ = lean_nat_dec_lt(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref(v_params_1609_);
lean_inc_ref(v_f_1515_);
v___x_1615_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1515_, v_type_1610_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; 
lean_dec_ref_known(v___x_1615_, 1);
lean_inc_ref(v_f_1515_);
v___x_1616_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1514_, v_f_1515_, v_value_1611_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_dec_ref_known(v___x_1616_, 1);
v_c_1516_ = v_k_1608_;
goto _start;
}
else
{
lean_dec_ref(v_k_1608_);
lean_dec_ref(v_f_1515_);
return v___x_1616_;
}
}
else
{
lean_dec_ref(v_value_1611_);
lean_dec_ref(v_k_1608_);
lean_dec_ref(v_f_1515_);
return v___x_1615_;
}
}
else
{
lean_object* v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1618_ = lean_box(0);
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = lean_usize_of_nat(v___x_1613_);
lean_inc_ref(v_f_1515_);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1514_, v_f_1515_, v_params_1609_, v___x_1619_, v___x_1620_, v___x_1618_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v_params_1609_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1621_, 1);
lean_inc_ref(v_f_1515_);
v___x_1622_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1515_, v_type_1610_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
lean_dec_ref_known(v___x_1622_, 1);
lean_inc_ref(v_f_1515_);
v___x_1623_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1514_, v_f_1515_, v_value_1611_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_dec_ref_known(v___x_1623_, 1);
v_c_1516_ = v_k_1608_;
goto _start;
}
else
{
lean_dec_ref(v_k_1608_);
lean_dec_ref(v_f_1515_);
return v___x_1623_;
}
}
else
{
lean_dec_ref(v_value_1611_);
lean_dec_ref(v_k_1608_);
lean_dec_ref(v_f_1515_);
return v___x_1622_;
}
}
else
{
lean_dec_ref(v_value_1611_);
lean_dec_ref(v_type_1610_);
lean_dec_ref(v_k_1608_);
lean_dec_ref(v_f_1515_);
return v___x_1621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1625_, lean_object* v_f_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1625_, v_f_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1636_, lean_object* v_f_1637_, lean_object* v_as_1638_, lean_object* v_i_1639_, lean_object* v_stop_1640_, lean_object* v_b_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_pu_boxed_1649_; size_t v_i_boxed_1650_; size_t v_stop_boxed_1651_; lean_object* v_res_1652_; 
v_pu_boxed_1649_ = lean_unbox(v_pu_1636_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1639_);
lean_dec(v_i_1639_);
v_stop_boxed_1651_ = lean_unbox_usize(v_stop_1640_);
lean_dec(v_stop_1640_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1649_, v_f_1637_, v_as_1638_, v_i_boxed_1650_, v_stop_boxed_1651_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v_as_1638_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1653_, lean_object* v_f_1654_, lean_object* v_c_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
uint8_t v_pu_boxed_1663_; lean_object* v_res_1664_; 
v_pu_boxed_1663_ = lean_unbox(v_pu_1653_);
v_res_1664_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1663_, v_f_1654_, v_c_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec(v___y_1656_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1665_, lean_object* v_as_1666_, size_t v_i_1667_, size_t v_stop_1668_, lean_object* v_b_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_usize_dec_eq(v_i_1667_, v_stop_1668_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_inc(v___x_1665_);
v___x_1678_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1678_, 0, v___x_1665_);
v___x_1679_ = lean_array_uget_borrowed(v_as_1666_, v_i_1667_);
lean_inc(v___x_1679_);
v___x_1680_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1678_, v___x_1679_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; size_t v___x_1682_; size_t v___x_1683_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1667_, v___x_1682_);
v_i_1667_ = v___x_1683_;
v_b_1669_ = v_a_1681_;
goto _start;
}
else
{
lean_dec(v___x_1665_);
return v___x_1680_;
}
}
else
{
lean_object* v___x_1685_; 
lean_dec(v___x_1665_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_b_1669_);
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1686_, lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_stop_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
size_t v_i_boxed_1698_; size_t v_stop_boxed_1699_; lean_object* v_res_1700_; 
v_i_boxed_1698_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_stop_boxed_1699_ = lean_unbox_usize(v_stop_1689_);
lean_dec(v_stop_1689_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1686_, v_as_1687_, v_i_boxed_1698_, v_stop_boxed_1699_, v_b_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v_as_1687_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = 0;
v___x_1710_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1701_);
lean_inc(v___x_1710_);
v___x_1711_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1711_, 0, v___x_1710_);
switch(lean_obj_tag(v_alt_1701_))
{
case 0:
{
lean_object* v_params_1712_; lean_object* v_code_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_params_1712_ = lean_ctor_get(v_alt_1701_, 1);
lean_inc_ref(v_params_1712_);
v_code_1713_ = lean_ctor_get(v_alt_1701_, 2);
lean_inc_ref(v_code_1713_);
lean_dec_ref_known(v_alt_1701_, 3);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_array_get_size(v_params_1712_);
v___x_1716_ = lean_nat_dec_lt(v___x_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v_params_1712_);
lean_dec(v___x_1710_);
v___x_1717_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1709_, v___x_1711_, v_code_1713_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = lean_box(0);
v___x_1719_ = ((size_t)0ULL);
v___x_1720_ = lean_usize_of_nat(v___x_1715_);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1710_, v_params_1712_, v___x_1719_, v___x_1720_, v___x_1718_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec_ref(v_params_1712_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref_known(v___x_1721_, 1);
v___x_1722_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1709_, v___x_1711_, v_code_1713_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v___x_1722_;
}
else
{
lean_dec_ref(v_code_1713_);
lean_dec_ref(v___x_1711_);
return v___x_1721_;
}
}
}
case 1:
{
lean_object* v_code_1723_; lean_object* v___x_1724_; 
lean_dec(v___x_1710_);
v_code_1723_ = lean_ctor_get(v_alt_1701_, 1);
lean_inc_ref(v_code_1723_);
lean_dec_ref_known(v_alt_1701_, 2);
v___x_1724_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1709_, v___x_1711_, v_code_1723_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v___x_1724_;
}
default: 
{
lean_object* v_code_1725_; lean_object* v___x_1726_; 
lean_dec(v___x_1710_);
v_code_1725_ = lean_ctor_get(v_alt_1701_, 0);
lean_inc_ref(v_code_1725_);
lean_dec_ref_known(v_alt_1701_, 1);
v___x_1726_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1709_, v___x_1711_, v_code_1725_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec(v_a_1728_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1736_, lean_object* v_f_1737_, lean_object* v_param_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1737_, v_param_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1747_, lean_object* v_f_1748_, lean_object* v_param_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v_pu_boxed_1757_; lean_object* v_res_1758_; 
v_pu_boxed_1757_ = lean_unbox(v_pu_1747_);
v_res_1758_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1757_, v_f_1748_, v_param_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1759_, lean_object* v_alt_1760_, lean_object* v_f_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1760_, v_f_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1770_, lean_object* v_alt_1771_, lean_object* v_f_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v_pu_boxed_1780_; lean_object* v_res_1781_; 
v_pu_boxed_1780_ = lean_unbox(v_pu_1770_);
v_res_1781_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1780_, v_alt_1771_, v_f_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec(v___y_1773_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1782_, lean_object* v_f_1783_, lean_object* v_arg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1783_, v_arg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1793_, lean_object* v_f_1794_, lean_object* v_arg_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v_pu_boxed_1803_; lean_object* v_res_1804_; 
v_pu_boxed_1803_ = lean_unbox(v_pu_1793_);
v_res_1804_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1803_, v_f_1794_, v_arg_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1805_, size_t v_i_1806_, size_t v_stop_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_usize_dec_eq(v_i_1806_, v_stop_1807_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_array_uget_borrowed(v_as_1805_, v_i_1806_);
lean_inc(v___x_1817_);
v___x_1818_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1817_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; size_t v___x_1820_; size_t v___x_1821_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1806_, v___x_1820_);
v_i_1806_ = v___x_1821_;
v_b_1808_ = v_a_1819_;
goto _start;
}
else
{
return v___x_1818_;
}
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_b_1808_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1824_, lean_object* v_i_1825_, lean_object* v_stop_1826_, lean_object* v_b_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
size_t v_i_boxed_1835_; size_t v_stop_boxed_1836_; lean_object* v_res_1837_; 
v_i_boxed_1835_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_stop_boxed_1836_ = lean_unbox_usize(v_stop_1826_);
lean_dec(v_stop_1826_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1824_, v_i_boxed_1835_, v_stop_boxed_1836_, v_b_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v_as_1824_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_alts_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_alts_1846_ = lean_ctor_get(v_cs_1838_, 3);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_alts_1846_);
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
return v___x_1851_;
}
else
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_nat_dec_le(v___x_1848_, v___x_1848_);
if (v___x_1852_ == 0)
{
if (v___x_1850_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1849_);
return v___x_1853_;
}
else
{
size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((size_t)0ULL);
v___x_1855_ = lean_usize_of_nat(v___x_1848_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1846_, v___x_1854_, v___x_1855_, v___x_1849_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
return v___x_1856_;
}
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_of_nat(v___x_1848_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1846_, v___x_1857_, v___x_1858_, v___x_1849_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
return v___x_1859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_cs_1860_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(lean_object* v_as_x27_1869_, lean_object* v_b_1870_){
_start:
{
if (lean_obj_tag(v_as_x27_1869_) == 0)
{
return v_b_1870_;
}
else
{
lean_object* v_head_1871_; lean_object* v_tail_1872_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; lean_object* v_r_1875_; 
v_head_1871_ = lean_ctor_get(v_as_x27_1869_, 0);
v_tail_1872_ = lean_ctor_get(v_as_x27_1869_, 1);
v_fst_1873_ = lean_ctor_get(v_head_1871_, 0);
v_snd_1874_ = lean_ctor_get(v_head_1871_, 1);
lean_inc(v_snd_1874_);
lean_inc(v_fst_1873_);
v_r_1875_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_b_1870_, v_fst_1873_, v_snd_1874_);
v_as_x27_1869_ = v_tail_1872_;
v_b_1870_ = v_r_1875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg___boxed(lean_object* v_as_x27_1877_, lean_object* v_b_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_as_x27_1877_, v_b_1878_);
lean_dec(v_as_x27_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(lean_object* v_m_1880_, lean_object* v_l_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_l_1881_, v_m_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___boxed(lean_object* v_m_1883_, lean_object* v_l_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(v_m_1883_, v_l_1884_);
lean_dec(v_l_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
if (lean_obj_tag(v_a_1886_) == 0)
{
lean_object* v___x_1888_; 
v___x_1888_ = l_List_reverse___redArg(v_a_1887_);
return v___x_1888_;
}
else
{
lean_object* v_head_1889_; lean_object* v_tail_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1901_; 
v_head_1889_ = lean_ctor_get(v_a_1886_, 0);
v_tail_1890_ = lean_ctor_get(v_a_1886_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1892_ = v_a_1886_;
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_tail_1890_);
lean_inc(v_head_1889_);
lean_dec(v_a_1886_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1894_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1889_);
lean_dec(v_head_1889_);
v___x_1895_ = lean_box(2);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v_a_1887_);
lean_ctor_set(v___x_1892_, 0, v___x_1896_);
v___x_1898_ = v___x_1892_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_a_1887_);
v___x_1898_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v_a_1886_ = v_tail_1890_;
v_a_1887_ = v___x_1898_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
if (lean_obj_tag(v_x_1903_) == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_x_1902_);
return v___x_1909_;
}
else
{
lean_object* v_head_1910_; lean_object* v_tail_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1973_; 
v_head_1910_ = lean_ctor_get(v_x_1903_, 0);
v_tail_1911_ = lean_ctor_get(v_x_1903_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1903_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1913_ = v_x_1903_;
v_isShared_1914_ = v_isSharedCheck_1973_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_tail_1911_);
lean_inc(v_head_1910_);
lean_dec(v_x_1903_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1973_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_fst_1915_; lean_object* v_snd_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1972_; 
v_fst_1915_ = lean_ctor_get(v_x_1902_, 0);
v_snd_1916_ = lean_ctor_get(v_x_1902_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1918_ = v_x_1902_;
v_isShared_1919_ = v_isSharedCheck_1972_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1916_);
lean_inc(v_fst_1915_);
lean_dec(v_x_1902_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1972_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; 
if (lean_obj_tag(v_head_1910_) == 0)
{
lean_object* v_decl_1953_; lean_object* v___x_1954_; 
v_decl_1953_ = lean_ctor_get(v_head_1910_, 0);
lean_inc_ref(v_decl_1953_);
v___x_1954_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_1953_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; uint8_t v___x_1956_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
if (v___x_1956_ == 0)
{
lean_del_object(v___x_1913_);
v___y_1921_ = v___y_1904_;
v___y_1922_ = v___y_1905_;
v___y_1923_ = v___y_1906_;
v___y_1924_ = v___y_1907_;
goto v___jp_1920_;
}
else
{
lean_object* v_fvarId_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
lean_inc_ref(v_decl_1953_);
lean_dec_ref_known(v_head_1910_, 1);
lean_del_object(v___x_1918_);
v_fvarId_1957_ = lean_ctor_get(v_decl_1953_, 0);
lean_inc(v_fvarId_1957_);
lean_dec_ref(v_decl_1953_);
v___x_1958_ = lean_box(2);
v___x_1959_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1915_, v_fvarId_1957_, v___x_1958_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 0);
lean_ctor_set(v___x_1913_, 1, v_snd_1916_);
lean_ctor_set(v___x_1913_, 0, v___x_1959_);
v___x_1961_ = v___x_1913_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_snd_1916_);
v___x_1961_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v_x_1902_ = v___x_1961_;
v_x_1903_ = v_tail_1911_;
goto _start;
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref_known(v_head_1910_, 1);
lean_del_object(v___x_1918_);
lean_dec(v_snd_1916_);
lean_dec(v_fst_1915_);
lean_del_object(v___x_1913_);
lean_dec(v_tail_1911_);
v_a_1964_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1954_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1954_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_del_object(v___x_1913_);
v___y_1921_ = v___y_1904_;
v___y_1922_ = v___y_1905_;
v___y_1923_ = v___y_1906_;
v___y_1924_ = v___y_1907_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_st_ref_get(v___y_1924_);
lean_dec(v___x_1925_);
v___x_1926_ = lean_st_mk_ref(v_snd_1916_);
lean_inc(v_head_1910_);
v___x_1927_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1910_, v___x_1926_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_st_ref_get(v___x_1926_);
lean_dec(v___x_1926_);
v___x_1930_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1931_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1910_);
lean_dec(v_head_1910_);
v___x_1932_ = lean_box(3);
v___x_1933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1915_, v___x_1931_, v___x_1932_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1929_);
lean_ctor_set(v___x_1918_, 0, v___x_1933_);
v___x_1935_ = v___x_1918_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1929_);
v___x_1935_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
v_x_1902_ = v___x_1935_;
v_x_1903_ = v_tail_1911_;
goto _start;
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1938_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1910_);
lean_dec(v_head_1910_);
v___x_1939_ = lean_box(2);
v___x_1940_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1915_, v___x_1938_, v___x_1939_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1929_);
lean_ctor_set(v___x_1918_, 0, v___x_1940_);
v___x_1942_ = v___x_1918_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1929_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_x_1902_ = v___x_1942_;
v_x_1903_ = v_tail_1911_;
goto _start;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v___x_1926_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1915_);
lean_dec(v_tail_1911_);
lean_dec(v_head_1910_);
v_a_1945_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1927_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1927_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_1974_, v_x_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1981_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_unsigned_to_nat(16u);
v___x_1984_ = lean_mk_array(v___x_1983_, v___x_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v___x_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_map_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v_typeName_2030_; lean_object* v_discr_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___y_2044_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_typeName_2030_ = lean_ctor_get(v_cs_1997_, 0);
v_discr_2031_ = lean_ctor_get(v_cs_1997_, 2);
v___x_2032_ = l_List_lengthTR___redArg(v_a_1998_);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_unsigned_to_nat(4u);
v___x_2035_ = lean_nat_mul(v___x_2032_, v___x_2034_);
lean_dec(v___x_2032_);
v___x_2036_ = lean_unsigned_to_nat(3u);
v___x_2037_ = lean_nat_div(v___x_2035_, v___x_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = l_Nat_nextPowerOfTwo(v___x_2037_);
lean_dec(v___x_2037_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_mk_array(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2033_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2064_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4));
v___x_2065_ = lean_name_eq(v_typeName_2030_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6));
v___x_2067_ = lean_name_eq(v_typeName_2030_, v___x_2066_);
v___y_2044_ = v___x_2067_;
goto v___jp_2043_;
}
else
{
v___y_2044_ = v___x_2065_;
goto v___jp_2043_;
}
v___jp_2004_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_st_mk_ref(v_map_2005_);
v___x_2012_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1997_, v___x_2011_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec_ref(v_cs_1997_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_2012_, 0);
lean_dec(v_unused_2021_);
v___x_2014_ = v___x_2012_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v___x_2012_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_st_ref_get(v___x_2011_);
lean_dec(v___x_2011_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v___x_2011_);
v_a_2022_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2012_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2012_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
v___jp_2043_:
{
if (v___y_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2041_);
lean_ctor_set(v___x_2045_, 1, v___x_2042_);
lean_inc(v_a_1998_);
v___x_2046_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2045_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v_fst_2048_; uint8_t v___x_2049_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v_fst_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc(v_fst_2048_);
lean_dec(v_a_2047_);
v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2048_, v_discr_2031_);
if (v___x_2049_ == 0)
{
v_map_2005_ = v_fst_2048_;
v___y_2006_ = v_a_1998_;
v___y_2007_ = v_a_1999_;
v___y_2008_ = v_a_2000_;
v___y_2009_ = v_a_2001_;
v___y_2010_ = v_a_2002_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_box(2);
lean_inc(v_discr_2031_);
v___x_2051_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2048_, v_discr_2031_, v___x_2050_);
v_map_2005_ = v___x_2051_;
v___y_2006_ = v_a_1998_;
v___y_2007_ = v_a_1999_;
v___y_2008_ = v_a_2000_;
v___y_2009_ = v_a_2001_;
v___y_2010_ = v_a_2002_;
goto v___jp_2004_;
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_cs_1997_);
v_a_2052_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2046_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2046_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref_known(v___x_2041_, 2);
lean_dec_ref(v_cs_1997_);
v___x_2060_ = lean_box(0);
lean_inc(v_a_1998_);
v___x_2061_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(v_a_1998_, v___x_2060_);
v___x_2062_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v___x_2061_, v___x_2042_);
lean_dec(v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2076_, v_x_2077_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2085_, v_x_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(lean_object* v_as_2094_, lean_object* v_as_x27_2095_, lean_object* v_b_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_as_x27_2095_, v_b_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___boxed(lean_object* v_as_2099_, lean_object* v_as_x27_2100_, lean_object* v_b_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(v_as_2099_, v_as_x27_2100_, v_b_2101_, v_a_2102_);
lean_dec(v_as_x27_2100_);
lean_dec(v_as_2099_);
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
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_nbuckets_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2174_ = lean_array_get_size(v_data_2173_);
v___x_2175_ = lean_unsigned_to_nat(2u);
v_nbuckets_2176_ = lean_nat_mul(v___x_2174_, v___x_2175_);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_mk_array(v_nbuckets_2176_, v___x_2178_);
v___x_2180_ = lean_array_propagate_mark(v_data_2173_, v___x_2179_);
v___x_2181_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2177_, v_data_2173_, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2182_, lean_object* v_a_2183_, lean_object* v_b_2184_){
_start:
{
lean_object* v_size_2185_; lean_object* v_buckets_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2229_; 
v_size_2185_ = lean_ctor_get(v_m_2182_, 0);
v_buckets_2186_ = lean_ctor_get(v_m_2182_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_m_2182_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2188_ = v_m_2182_;
v_isShared_2189_ = v_isSharedCheck_2229_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_buckets_2186_);
lean_inc(v_size_2185_);
lean_dec(v_m_2182_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2229_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; uint64_t v___x_2191_; uint64_t v___x_2192_; uint64_t v___x_2193_; uint64_t v_fold_2194_; uint64_t v___x_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; lean_object* v_bkt_2203_; uint8_t v___x_2204_; 
v___x_2190_ = lean_array_get_size(v_buckets_2186_);
v___x_2191_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2183_);
v___x_2192_ = 32ULL;
v___x_2193_ = lean_uint64_shift_right(v___x_2191_, v___x_2192_);
v_fold_2194_ = lean_uint64_xor(v___x_2191_, v___x_2193_);
v___x_2195_ = 16ULL;
v___x_2196_ = lean_uint64_shift_right(v_fold_2194_, v___x_2195_);
v___x_2197_ = lean_uint64_xor(v_fold_2194_, v___x_2196_);
v___x_2198_ = lean_uint64_to_usize(v___x_2197_);
v___x_2199_ = lean_usize_of_nat(v___x_2190_);
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_sub(v___x_2199_, v___x_2200_);
v___x_2202_ = lean_usize_land(v___x_2198_, v___x_2201_);
v_bkt_2203_ = lean_array_uget_borrowed(v_buckets_2186_, v___x_2202_);
v___x_2204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2183_, v_bkt_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v_size_x27_2206_; lean_object* v___x_2207_; lean_object* v_buckets_x27_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v_size_x27_2206_ = lean_nat_add(v_size_2185_, v___x_2205_);
lean_dec(v_size_2185_);
lean_inc(v_bkt_2203_);
v___x_2207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2207_, 0, v_a_2183_);
lean_ctor_set(v___x_2207_, 1, v_b_2184_);
lean_ctor_set(v___x_2207_, 2, v_bkt_2203_);
v_buckets_x27_2208_ = lean_array_uset(v_buckets_2186_, v___x_2202_, v___x_2207_);
v___x_2209_ = lean_unsigned_to_nat(4u);
v___x_2210_ = lean_nat_mul(v_size_x27_2206_, v___x_2209_);
v___x_2211_ = lean_unsigned_to_nat(3u);
v___x_2212_ = lean_nat_div(v___x_2210_, v___x_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_array_get_size(v_buckets_x27_2208_);
v___x_2214_ = lean_nat_dec_le(v___x_2212_, v___x_2213_);
lean_dec(v___x_2212_);
if (v___x_2214_ == 0)
{
lean_object* v_val_2215_; lean_object* v___x_2217_; 
v_val_2215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2208_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v_val_2215_);
lean_ctor_set(v___x_2188_, 0, v_size_x27_2206_);
v___x_2217_ = v___x_2188_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_size_x27_2206_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_val_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v___x_2220_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v_buckets_x27_2208_);
lean_ctor_set(v___x_2188_, 0, v_size_x27_2206_);
v___x_2220_ = v___x_2188_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_size_x27_2206_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_buckets_x27_2208_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
else
{
lean_object* v___x_2222_; lean_object* v_buckets_x27_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_inc(v_bkt_2203_);
v___x_2222_ = lean_box(0);
v_buckets_x27_2223_ = lean_array_uset(v_buckets_2186_, v___x_2202_, v___x_2222_);
v___x_2224_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2183_, v_b_2184_, v_bkt_2203_);
v___x_2225_ = lean_array_uset(v_buckets_x27_2223_, v___x_2202_, v___x_2224_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v___x_2225_);
v___x_2227_ = v___x_2188_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_size_2185_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2230_, size_t v_i_2231_, size_t v_stop_2232_, lean_object* v_b_2233_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_usize_dec_eq(v_i_2231_, v_stop_2232_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = ((size_t)1ULL);
v___x_2237_ = lean_usize_sub(v_i_2231_, v___x_2236_);
v___x_2238_ = lean_array_uget_borrowed(v_as_2230_, v___x_2237_);
v___x_2239_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2238_);
v___x_2240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2233_, v___x_2239_, v___x_2235_);
v_i_2231_ = v___x_2237_;
v_b_2233_ = v___x_2240_;
goto _start;
}
else
{
return v_b_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2242_, lean_object* v_i_2243_, lean_object* v_stop_2244_, lean_object* v_b_2245_){
_start:
{
size_t v_i_boxed_2246_; size_t v_stop_boxed_2247_; lean_object* v_res_2248_; 
v_i_boxed_2246_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_stop_boxed_2247_ = lean_unbox_usize(v_stop_2244_);
lean_dec(v_stop_2244_);
v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2242_, v_i_boxed_2246_, v_stop_boxed_2247_, v_b_2245_);
lean_dec_ref(v_as_2242_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2249_){
_start:
{
lean_object* v_alts_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_map_2265_; uint8_t v___x_2266_; 
v_alts_2250_ = lean_ctor_get(v_cs_2249_, 3);
v___x_2251_ = lean_array_get_size(v_alts_2250_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_add(v___x_2251_, v___x_2252_);
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = lean_unsigned_to_nat(4u);
v___x_2256_ = lean_nat_mul(v___x_2253_, v___x_2255_);
lean_dec(v___x_2253_);
v___x_2257_ = lean_unsigned_to_nat(3u);
v___x_2258_ = lean_nat_div(v___x_2256_, v___x_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = l_Nat_nextPowerOfTwo(v___x_2258_);
lean_dec(v___x_2258_);
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_mk_array(v___x_2259_, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2254_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_box(2);
v___x_2264_ = lean_box(0);
v_map_2265_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2262_, v___x_2263_, v___x_2264_);
v___x_2266_ = lean_nat_dec_lt(v___x_2254_, v___x_2251_);
if (v___x_2266_ == 0)
{
return v_map_2265_;
}
else
{
size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_usize_of_nat(v___x_2251_);
v___x_2268_ = ((size_t)0ULL);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2250_, v___x_2267_, v___x_2268_, v_map_2265_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2270_);
lean_dec_ref(v_cs_2270_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2272_, lean_object* v_m_2273_, lean_object* v_a_2274_, lean_object* v_b_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2273_, v_a_2274_, v_b_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2277_, lean_object* v_a_2278_, lean_object* v_x_2279_){
_start:
{
uint8_t v___x_2280_; 
v___x_2280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2278_, v_x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2281_, lean_object* v_a_2282_, lean_object* v_x_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2281_, v_a_2282_, v_x_2283_);
lean_dec(v_x_2283_);
lean_dec(v_a_2282_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2286_, lean_object* v_data_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2289_, lean_object* v_a_2290_, lean_object* v_b_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2290_, v_b_2291_, v_x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2294_, lean_object* v_i_2295_, lean_object* v_source_2296_, lean_object* v_target_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2295_, v_source_2296_, v_target_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2300_, v_x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v_decision_2307_; uint8_t v___x_2308_; 
v___x_2306_ = lean_st_ref_get(v_a_2304_);
v_decision_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc_ref(v_decision_2307_);
lean_dec(v___x_2306_);
v___x_2308_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2307_, v_fvar_2303_);
lean_dec_ref(v_decision_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec(v_fvar_2303_);
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
else
{
lean_object* v___x_2311_; lean_object* v_decision_2312_; lean_object* v_newArms_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2325_; 
v___x_2311_ = lean_st_ref_take(v_a_2304_);
v_decision_2312_ = lean_ctor_get(v___x_2311_, 0);
v_newArms_2313_ = lean_ctor_get(v___x_2311_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2315_ = v___x_2311_;
v_isShared_2316_ = v_isSharedCheck_2325_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_newArms_2313_);
lean_inc(v_decision_2312_);
lean_dec(v___x_2311_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2325_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_box(2);
v___x_2318_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2312_, v_fvar_2303_, v___x_2317_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_newArms_2313_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_st_ref_put(v_a_2304_, v___x_2320_);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2326_, v_a_2327_);
lean_dec(v_a_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2330_, v_a_2331_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec(v_a_2340_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v_toApplicative_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2421_; 
v___x_2356_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2357_ = l_StateRefT_x27_instMonad___redArg(v___x_2356_);
v_toApplicative_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v___x_2357_, 1);
lean_dec(v_unused_2422_);
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2421_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_toApplicative_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2421_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_toFunctor_2362_; lean_object* v_toSeq_2363_; lean_object* v_toSeqLeft_2364_; lean_object* v_toSeqRight_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2419_; 
v_toFunctor_2362_ = lean_ctor_get(v_toApplicative_2358_, 0);
v_toSeq_2363_ = lean_ctor_get(v_toApplicative_2358_, 2);
v_toSeqLeft_2364_ = lean_ctor_get(v_toApplicative_2358_, 3);
v_toSeqRight_2365_ = lean_ctor_get(v_toApplicative_2358_, 4);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_toApplicative_2358_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v_toApplicative_2358_, 1);
lean_dec(v_unused_2420_);
v___x_2367_ = v_toApplicative_2358_;
v_isShared_2368_ = v_isSharedCheck_2419_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_toSeqRight_2365_);
lean_inc(v_toSeqLeft_2364_);
lean_inc(v_toSeq_2363_);
lean_inc(v_toFunctor_2362_);
lean_dec(v_toApplicative_2358_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2419_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___f_2369_; lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___x_2378_; 
v___f_2369_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2370_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2362_);
v___f_2371_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2371_, 0, v_toFunctor_2362_);
v___f_2372_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2372_, 0, v_toFunctor_2362_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___f_2371_);
lean_ctor_set(v___x_2373_, 1, v___f_2372_);
v___f_2374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2374_, 0, v_toSeqRight_2365_);
v___f_2375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2375_, 0, v_toSeqLeft_2364_);
v___f_2376_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2376_, 0, v_toSeq_2363_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 4, v___f_2374_);
lean_ctor_set(v___x_2367_, 3, v___f_2375_);
lean_ctor_set(v___x_2367_, 2, v___f_2376_);
lean_ctor_set(v___x_2367_, 1, v___f_2369_);
lean_ctor_set(v___x_2367_, 0, v___x_2373_);
v___x_2378_ = v___x_2367_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___f_2369_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v___f_2376_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v___f_2375_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v___f_2374_);
v___x_2378_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2380_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___f_2370_);
lean_ctor_set(v___x_2360_, 0, v___x_2378_);
v___x_2380_ = v___x_2360_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___f_2370_);
v___x_2380_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v_toApplicative_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2415_; 
v___x_2381_ = l_StateRefT_x27_instMonad___redArg(v___x_2380_);
v_toApplicative_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v___x_2381_, 1);
lean_dec(v_unused_2416_);
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2415_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_toApplicative_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2415_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_toFunctor_2386_; lean_object* v_toSeq_2387_; lean_object* v_toSeqLeft_2388_; lean_object* v_toSeqRight_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2413_; 
v_toFunctor_2386_ = lean_ctor_get(v_toApplicative_2382_, 0);
v_toSeq_2387_ = lean_ctor_get(v_toApplicative_2382_, 2);
v_toSeqLeft_2388_ = lean_ctor_get(v_toApplicative_2382_, 3);
v_toSeqRight_2389_ = lean_ctor_get(v_toApplicative_2382_, 4);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_toApplicative_2382_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v_toApplicative_2382_, 1);
lean_dec(v_unused_2414_);
v___x_2391_ = v_toApplicative_2382_;
v_isShared_2392_ = v_isSharedCheck_2413_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_toSeqRight_2389_);
lean_inc(v_toSeqLeft_2388_);
lean_inc(v_toSeq_2387_);
lean_inc(v_toFunctor_2386_);
lean_dec(v_toApplicative_2382_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2413_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___f_2393_; lean_object* v___f_2394_; lean_object* v___f_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___f_2398_; lean_object* v___f_2399_; lean_object* v___f_2400_; lean_object* v___x_2402_; 
v___f_2393_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2394_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2386_);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2395_, 0, v_toFunctor_2386_);
v___f_2396_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2396_, 0, v_toFunctor_2386_);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___f_2395_);
lean_ctor_set(v___x_2397_, 1, v___f_2396_);
v___f_2398_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2398_, 0, v_toSeqRight_2389_);
v___f_2399_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2399_, 0, v_toSeqLeft_2388_);
v___f_2400_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2400_, 0, v_toSeq_2387_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 4, v___f_2398_);
lean_ctor_set(v___x_2391_, 3, v___f_2399_);
lean_ctor_set(v___x_2391_, 2, v___f_2400_);
lean_ctor_set(v___x_2391_, 1, v___f_2393_);
lean_ctor_set(v___x_2391_, 0, v___x_2397_);
v___x_2402_ = v___x_2391_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___f_2393_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v___f_2400_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v___f_2399_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v___f_2398_);
v___x_2402_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2404_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___f_2394_);
lean_ctor_set(v___x_2384_, 0, v___x_2402_);
v___x_2404_ = v___x_2384_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___f_2394_);
v___x_2404_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_10720__overap_2409_; lean_object* v___x_2410_; 
v___x_2405_ = l_ReaderT_instMonad___redArg(v___x_2404_);
v___x_2406_ = l_StateRefT_x27_instMonad___redArg(v___x_2405_);
v___x_2407_ = lean_box(0);
v___x_2408_ = l_instInhabitedOfMonad___redArg(v___x_2406_, v___x_2407_);
v___x_10720__overap_2409_ = lean_panic_fn_borrowed(v___x_2408_, v_msg_2348_);
lean_dec(v___x_2408_);
lean_inc(v___y_2354_);
lean_inc_ref(v___y_2353_);
lean_inc(v___y_2352_);
lean_inc_ref(v___y_2351_);
lean_inc(v___y_2350_);
lean_inc(v___y_2349_);
v___x_2410_ = lean_apply_7(v___x_10720__overap_2409_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, lean_box(0));
return v___x_2410_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec(v___y_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2432_, lean_object* v_e_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_ty_2442_; lean_object* v_body_2443_; uint8_t v___x_2446_; 
v___x_2446_ = l_Lean_Expr_hasFVar(v_e_2433_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref(v_e_2433_);
lean_dec_ref(v_f_2432_);
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
else
{
switch(lean_obj_tag(v_e_2433_))
{
case 1:
{
lean_object* v_fvarId_2449_; lean_object* v___x_2450_; 
v_fvarId_2449_ = lean_ctor_get(v_e_2433_, 0);
lean_inc(v_fvarId_2449_);
lean_dec_ref_known(v_e_2433_, 1);
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2438_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2436_);
lean_inc(v___y_2435_);
lean_inc(v___y_2434_);
v___x_2450_ = lean_apply_8(v_f_2432_, v_fvarId_2449_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, lean_box(0));
return v___x_2450_;
}
case 2:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_dec_ref_known(v_e_2433_, 1);
lean_dec_ref(v_f_2432_);
v___x_2451_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2452_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2451_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2452_;
}
case 5:
{
lean_object* v_fn_2453_; lean_object* v_arg_2454_; lean_object* v___x_2455_; 
v_fn_2453_ = lean_ctor_get(v_e_2433_, 0);
lean_inc_ref(v_fn_2453_);
v_arg_2454_ = lean_ctor_get(v_e_2433_, 1);
lean_inc_ref(v_arg_2454_);
lean_dec_ref_known(v_e_2433_, 2);
lean_inc_ref(v_f_2432_);
v___x_2455_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2432_, v_fn_2453_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_dec_ref_known(v___x_2455_, 1);
v_e_2433_ = v_arg_2454_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2454_);
lean_dec_ref(v_f_2432_);
return v___x_2455_;
}
}
case 6:
{
lean_object* v_binderType_2457_; lean_object* v_body_2458_; 
v_binderType_2457_ = lean_ctor_get(v_e_2433_, 1);
lean_inc_ref(v_binderType_2457_);
v_body_2458_ = lean_ctor_get(v_e_2433_, 2);
lean_inc_ref(v_body_2458_);
lean_dec_ref_known(v_e_2433_, 3);
v_ty_2442_ = v_binderType_2457_;
v_body_2443_ = v_body_2458_;
goto v___jp_2441_;
}
case 7:
{
lean_object* v_binderType_2459_; lean_object* v_body_2460_; 
v_binderType_2459_ = lean_ctor_get(v_e_2433_, 1);
lean_inc_ref(v_binderType_2459_);
v_body_2460_ = lean_ctor_get(v_e_2433_, 2);
lean_inc_ref(v_body_2460_);
lean_dec_ref_known(v_e_2433_, 3);
v_ty_2442_ = v_binderType_2459_;
v_body_2443_ = v_body_2460_;
goto v___jp_2441_;
}
case 8:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref_known(v_e_2433_, 4);
lean_dec_ref(v_f_2432_);
v___x_2461_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2462_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2461_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2462_;
}
case 11:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec_ref_known(v_e_2433_, 3);
lean_dec_ref(v_f_2432_);
v___x_2463_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2464_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2463_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2464_;
}
default: 
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec_ref(v_e_2433_);
lean_dec_ref(v_f_2432_);
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
}
}
v___jp_2441_:
{
lean_object* v___x_2444_; 
lean_inc_ref(v_f_2432_);
v___x_2444_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2432_, v_ty_2442_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_dec_ref_known(v___x_2444_, 1);
v_e_2433_ = v_body_2443_;
goto _start;
}
else
{
lean_dec_ref(v_body_2443_);
lean_dec_ref(v_f_2432_);
return v___x_2444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2467_, lean_object* v_e_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2467_, v_e_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v___y_2469_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2477_, lean_object* v_arg_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
switch(lean_obj_tag(v_arg_2478_))
{
case 0:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v_f_2477_);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
case 1:
{
lean_object* v_fvarId_2488_; lean_object* v___x_2489_; 
v_fvarId_2488_ = lean_ctor_get(v_arg_2478_, 0);
lean_inc(v_fvarId_2488_);
lean_dec_ref_known(v_arg_2478_, 1);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
lean_inc(v___y_2480_);
lean_inc(v___y_2479_);
v___x_2489_ = lean_apply_8(v_f_2477_, v_fvarId_2488_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, lean_box(0));
return v___x_2489_;
}
default: 
{
lean_object* v_expr_2490_; lean_object* v___x_2491_; 
v_expr_2490_ = lean_ctor_get(v_arg_2478_, 0);
lean_inc_ref(v_expr_2490_);
lean_dec_ref_known(v_arg_2478_, 1);
v___x_2491_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2477_, v_expr_2490_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2492_, lean_object* v_arg_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2492_, v_arg_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec(v___y_2494_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2502_, lean_object* v_param_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_type_2511_; lean_object* v___x_2512_; 
v_type_2511_ = lean_ctor_get(v_param_2503_, 2);
lean_inc_ref(v_type_2511_);
lean_dec_ref(v_param_2503_);
v___x_2512_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2502_, v_type_2511_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2513_, lean_object* v_param_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2513_, v_param_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2523_, lean_object* v_f_2524_, lean_object* v_as_2525_, size_t v_i_2526_, size_t v_stop_2527_, lean_object* v_b_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_eq(v_i_2526_, v_stop_2527_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_array_uget_borrowed(v_as_2525_, v_i_2526_);
lean_inc(v___x_2537_);
lean_inc_ref(v_f_2524_);
v___x_2538_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2524_, v___x_2537_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; size_t v___x_2540_; size_t v___x_2541_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2540_ = ((size_t)1ULL);
v___x_2541_ = lean_usize_add(v_i_2526_, v___x_2540_);
v_i_2526_ = v___x_2541_;
v_b_2528_ = v_a_2539_;
goto _start;
}
else
{
lean_dec_ref(v_f_2524_);
return v___x_2538_;
}
}
else
{
lean_object* v___x_2543_; 
lean_dec_ref(v_f_2524_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_b_2528_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2544_, lean_object* v_f_2545_, lean_object* v_as_2546_, lean_object* v_i_2547_, lean_object* v_stop_2548_, lean_object* v_b_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v_pu_boxed_2557_; size_t v_i_boxed_2558_; size_t v_stop_boxed_2559_; lean_object* v_res_2560_; 
v_pu_boxed_2557_ = lean_unbox(v_pu_2544_);
v_i_boxed_2558_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_stop_boxed_2559_ = lean_unbox_usize(v_stop_2548_);
lean_dec(v_stop_2548_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2557_, v_f_2545_, v_as_2546_, v_i_boxed_2558_, v_stop_boxed_2559_, v_b_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v_as_2546_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2561_, lean_object* v_f_2562_, lean_object* v_as_2563_, size_t v_i_2564_, size_t v_stop_2565_, lean_object* v_b_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_eq(v_i_2564_, v_stop_2565_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_array_uget_borrowed(v_as_2563_, v_i_2564_);
lean_inc(v___x_2575_);
lean_inc_ref(v_f_2562_);
v___x_2576_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2562_, v___x_2575_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; size_t v___x_2578_; size_t v___x_2579_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = ((size_t)1ULL);
v___x_2579_ = lean_usize_add(v_i_2564_, v___x_2578_);
v_i_2564_ = v___x_2579_;
v_b_2566_ = v_a_2577_;
goto _start;
}
else
{
lean_dec_ref(v_f_2562_);
return v___x_2576_;
}
}
else
{
lean_object* v___x_2581_; 
lean_dec_ref(v_f_2562_);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_b_2566_);
return v___x_2581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2582_, lean_object* v_f_2583_, lean_object* v_as_2584_, lean_object* v_i_2585_, lean_object* v_stop_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v_pu_boxed_2595_; size_t v_i_boxed_2596_; size_t v_stop_boxed_2597_; lean_object* v_res_2598_; 
v_pu_boxed_2595_ = lean_unbox(v_pu_2582_);
v_i_boxed_2596_ = lean_unbox_usize(v_i_2585_);
lean_dec(v_i_2585_);
v_stop_boxed_2597_ = lean_unbox_usize(v_stop_2586_);
lean_dec(v_stop_2586_);
v_res_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2595_, v_f_2583_, v_as_2584_, v_i_boxed_2596_, v_stop_boxed_2597_, v_b_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v_as_2584_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2599_, lean_object* v_f_2600_, lean_object* v_e_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_args_2610_; 
switch(lean_obj_tag(v_e_2601_))
{
case 2:
{
lean_object* v_struct_2619_; lean_object* v___x_2620_; 
v_struct_2619_ = lean_ctor_get(v_e_2601_, 2);
lean_inc(v_struct_2619_);
lean_dec_ref_known(v_e_2601_, 3);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2620_ = lean_apply_8(v_f_2600_, v_struct_2619_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2620_;
}
case 3:
{
lean_object* v_args_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_args_2621_ = lean_ctor_get(v_e_2601_, 2);
lean_inc_ref(v_args_2621_);
lean_dec_ref_known(v_e_2601_, 3);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_array_get_size(v_args_2621_);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_nat_dec_lt(v___x_2622_, v___x_2623_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v_args_2621_);
lean_dec_ref(v_f_2600_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2624_);
return v___x_2626_;
}
else
{
size_t v___x_2627_; size_t v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = lean_usize_of_nat(v___x_2623_);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2599_, v_f_2600_, v_args_2621_, v___x_2627_, v___x_2628_, v___x_2624_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_args_2621_);
return v___x_2629_;
}
}
case 4:
{
lean_object* v_fvarId_2630_; lean_object* v_args_2631_; lean_object* v___x_2632_; 
v_fvarId_2630_ = lean_ctor_get(v_e_2601_, 0);
lean_inc(v_fvarId_2630_);
v_args_2631_ = lean_ctor_get(v_e_2601_, 1);
lean_inc_ref(v_args_2631_);
lean_dec_ref_known(v_e_2601_, 2);
lean_inc_ref(v_f_2600_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2632_ = lean_apply_8(v_f_2600_, v_fvarId_2630_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2646_; 
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v___x_2632_, 0);
lean_dec(v_unused_2647_);
v___x_2634_ = v___x_2632_;
v_isShared_2635_ = v_isSharedCheck_2646_;
goto v_resetjp_2633_;
}
else
{
lean_dec(v___x_2632_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2646_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_array_get_size(v_args_2631_);
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_nat_dec_lt(v___x_2636_, v___x_2637_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref(v_args_2631_);
lean_dec_ref(v_f_2600_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2638_);
v___x_2641_ = v___x_2634_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2638_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
else
{
size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
lean_del_object(v___x_2634_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = lean_usize_of_nat(v___x_2637_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2599_, v_f_2600_, v_args_2631_, v___x_2643_, v___x_2644_, v___x_2638_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_args_2631_);
return v___x_2645_;
}
}
}
else
{
lean_dec_ref(v_args_2631_);
lean_dec_ref(v_f_2600_);
return v___x_2632_;
}
}
case 5:
{
lean_object* v_args_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_args_2648_ = lean_ctor_get(v_e_2601_, 1);
lean_inc_ref(v_args_2648_);
lean_dec_ref_known(v_e_2601_, 2);
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_array_get_size(v_args_2648_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_nat_dec_lt(v___x_2649_, v___x_2650_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref(v_args_2648_);
lean_dec_ref(v_f_2600_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
return v___x_2653_;
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = lean_usize_of_nat(v___x_2650_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2599_, v_f_2600_, v_args_2648_, v___x_2654_, v___x_2655_, v___x_2651_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_args_2648_);
return v___x_2656_;
}
}
case 6:
{
lean_object* v_var_2657_; lean_object* v___x_2658_; 
v_var_2657_ = lean_ctor_get(v_e_2601_, 1);
lean_inc(v_var_2657_);
lean_dec_ref_known(v_e_2601_, 2);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2658_ = lean_apply_8(v_f_2600_, v_var_2657_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2658_;
}
case 7:
{
lean_object* v_var_2659_; lean_object* v___x_2660_; 
v_var_2659_ = lean_ctor_get(v_e_2601_, 1);
lean_inc(v_var_2659_);
lean_dec_ref_known(v_e_2601_, 2);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2660_ = lean_apply_8(v_f_2600_, v_var_2659_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2660_;
}
case 8:
{
lean_object* v_var_2661_; lean_object* v___x_2662_; 
v_var_2661_ = lean_ctor_get(v_e_2601_, 2);
lean_inc(v_var_2661_);
lean_dec_ref_known(v_e_2601_, 3);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2662_ = lean_apply_8(v_f_2600_, v_var_2661_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2662_;
}
case 9:
{
lean_object* v_args_2663_; 
v_args_2663_ = lean_ctor_get(v_e_2601_, 1);
lean_inc_ref(v_args_2663_);
lean_dec_ref_known(v_e_2601_, 2);
v_args_2610_ = v_args_2663_;
goto v___jp_2609_;
}
case 10:
{
lean_object* v_args_2664_; 
v_args_2664_ = lean_ctor_get(v_e_2601_, 1);
lean_inc_ref(v_args_2664_);
lean_dec_ref_known(v_e_2601_, 2);
v_args_2610_ = v_args_2664_;
goto v___jp_2609_;
}
case 11:
{
lean_object* v_var_2665_; lean_object* v___x_2666_; 
v_var_2665_ = lean_ctor_get(v_e_2601_, 1);
lean_inc(v_var_2665_);
lean_dec_ref_known(v_e_2601_, 2);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2666_ = lean_apply_8(v_f_2600_, v_var_2665_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2666_;
}
case 12:
{
lean_object* v_var_2667_; lean_object* v_args_2668_; lean_object* v___x_2669_; 
v_var_2667_ = lean_ctor_get(v_e_2601_, 0);
lean_inc(v_var_2667_);
v_args_2668_ = lean_ctor_get(v_e_2601_, 2);
lean_inc_ref(v_args_2668_);
lean_dec_ref_known(v_e_2601_, 3);
lean_inc_ref(v_f_2600_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2669_ = lean_apply_8(v_f_2600_, v_var_2667_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2683_; 
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2669_, 0);
lean_dec(v_unused_2684_);
v___x_2671_ = v___x_2669_;
v_isShared_2672_ = v_isSharedCheck_2683_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2669_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2683_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_array_get_size(v_args_2668_);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_nat_dec_lt(v___x_2673_, v___x_2674_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v_args_2668_);
lean_dec_ref(v_f_2600_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2675_);
v___x_2678_ = v___x_2671_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2675_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
lean_del_object(v___x_2671_);
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2674_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2599_, v_f_2600_, v_args_2668_, v___x_2680_, v___x_2681_, v___x_2675_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_args_2668_);
return v___x_2682_;
}
}
}
else
{
lean_dec_ref(v_args_2668_);
lean_dec_ref(v_f_2600_);
return v___x_2669_;
}
}
case 13:
{
lean_object* v_fvarId_2685_; lean_object* v___x_2686_; 
v_fvarId_2685_ = lean_ctor_get(v_e_2601_, 1);
lean_inc(v_fvarId_2685_);
lean_dec_ref_known(v_e_2601_, 2);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2686_ = lean_apply_8(v_f_2600_, v_fvarId_2685_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2686_;
}
case 14:
{
lean_object* v_fvarId_2687_; lean_object* v___x_2688_; 
v_fvarId_2687_ = lean_ctor_get(v_e_2601_, 0);
lean_inc(v_fvarId_2687_);
lean_dec_ref_known(v_e_2601_, 1);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2688_ = lean_apply_8(v_f_2600_, v_fvarId_2687_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2688_;
}
case 15:
{
lean_object* v_fvarId_2689_; lean_object* v___x_2690_; 
v_fvarId_2689_ = lean_ctor_get(v_e_2601_, 0);
lean_inc(v_fvarId_2689_);
lean_dec_ref_known(v_e_2601_, 1);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2690_ = lean_apply_8(v_f_2600_, v_fvarId_2689_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, lean_box(0));
return v___x_2690_;
}
default: 
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v_e_2601_);
lean_dec_ref(v_f_2600_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
return v___x_2692_;
}
}
v___jp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_array_get_size(v_args_2610_);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_nat_dec_lt(v___x_2611_, v___x_2612_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
lean_dec_ref(v_args_2610_);
lean_dec_ref(v_f_2600_);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
return v___x_2615_;
}
else
{
size_t v___x_2616_; size_t v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = ((size_t)0ULL);
v___x_2617_ = lean_usize_of_nat(v___x_2612_);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2599_, v_f_2600_, v_args_2610_, v___x_2616_, v___x_2617_, v___x_2613_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_args_2610_);
return v___x_2618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2693_, lean_object* v_f_2694_, lean_object* v_e_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
uint8_t v_pu_boxed_2703_; lean_object* v_res_2704_; 
v_pu_boxed_2703_ = lean_unbox(v_pu_2693_);
v_res_2704_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2703_, v_f_2694_, v_e_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2705_, lean_object* v_f_2706_, lean_object* v_decl_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_type_2715_; lean_object* v_value_2716_; lean_object* v___x_2717_; 
v_type_2715_ = lean_ctor_get(v_decl_2707_, 2);
lean_inc_ref(v_type_2715_);
v_value_2716_ = lean_ctor_get(v_decl_2707_, 3);
lean_inc(v_value_2716_);
lean_dec_ref(v_decl_2707_);
lean_inc_ref(v_f_2706_);
v___x_2717_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2706_, v_type_2715_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2718_; 
lean_dec_ref_known(v___x_2717_, 1);
v___x_2718_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2705_, v_f_2706_, v_value_2716_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2718_;
}
else
{
lean_dec(v_value_2716_);
lean_dec_ref(v_f_2706_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2719_, lean_object* v_f_2720_, lean_object* v_decl_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v_pu_boxed_2729_; lean_object* v_res_2730_; 
v_pu_boxed_2729_ = lean_unbox(v_pu_2719_);
v_res_2730_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2729_, v_f_2720_, v_decl_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec(v___y_2722_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2731_, lean_object* v_f_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
switch(lean_obj_tag(v_alt_2731_))
{
case 0:
{
lean_object* v_code_2740_; lean_object* v___x_2741_; 
v_code_2740_ = lean_ctor_get(v_alt_2731_, 2);
lean_inc_ref(v_code_2740_);
lean_dec_ref_known(v_alt_2731_, 3);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc(v___y_2733_);
v___x_2741_ = lean_apply_8(v_f_2732_, v_code_2740_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, lean_box(0));
return v___x_2741_;
}
case 1:
{
lean_object* v_code_2742_; lean_object* v___x_2743_; 
v_code_2742_ = lean_ctor_get(v_alt_2731_, 1);
lean_inc_ref(v_code_2742_);
lean_dec_ref_known(v_alt_2731_, 2);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc(v___y_2733_);
v___x_2743_ = lean_apply_8(v_f_2732_, v_code_2742_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, lean_box(0));
return v___x_2743_;
}
default: 
{
lean_object* v_code_2744_; lean_object* v___x_2745_; 
v_code_2744_ = lean_ctor_get(v_alt_2731_, 0);
lean_inc_ref(v_code_2744_);
lean_dec_ref_known(v_alt_2731_, 1);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc(v___y_2733_);
v___x_2745_ = lean_apply_8(v_f_2732_, v_code_2744_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, lean_box(0));
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2746_, lean_object* v_f_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2746_, v_f_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2756_, lean_object* v_f_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
uint8_t v_pu_boxed_2766_; lean_object* v_res_2767_; 
v_pu_boxed_2766_ = lean_unbox(v_pu_2756_);
v_res_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2766_, v_f_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec(v___y_2759_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2768_, lean_object* v_f_2769_, lean_object* v_as_2770_, size_t v_i_2771_, size_t v_stop_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_usize_dec_eq(v_i_2771_, v_stop_2772_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___f_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2782_ = lean_box(v_pu_2768_);
lean_inc_ref(v_f_2769_);
v___f_2783_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2783_, 0, v___x_2782_);
lean_closure_set(v___f_2783_, 1, v_f_2769_);
v___x_2784_ = lean_array_uget_borrowed(v_as_2770_, v_i_2771_);
lean_inc(v___x_2784_);
v___x_2785_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2784_, v___f_2783_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; size_t v___x_2787_; size_t v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = ((size_t)1ULL);
v___x_2788_ = lean_usize_add(v_i_2771_, v___x_2787_);
v_i_2771_ = v___x_2788_;
v_b_2773_ = v_a_2786_;
goto _start;
}
else
{
lean_dec_ref(v_f_2769_);
return v___x_2785_;
}
}
else
{
lean_object* v___x_2790_; 
lean_dec_ref(v_f_2769_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_b_2773_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2791_, lean_object* v_f_2792_, lean_object* v_c_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
switch(lean_obj_tag(v_c_2793_))
{
case 0:
{
lean_object* v_decl_2801_; lean_object* v_k_2802_; lean_object* v___x_2803_; 
v_decl_2801_ = lean_ctor_get(v_c_2793_, 0);
lean_inc_ref(v_decl_2801_);
v_k_2802_ = lean_ctor_get(v_c_2793_, 1);
lean_inc_ref(v_k_2802_);
lean_dec_ref_known(v_c_2793_, 2);
lean_inc_ref(v_f_2792_);
v___x_2803_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2791_, v_f_2792_, v_decl_2801_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_dec_ref_known(v___x_2803_, 1);
v_c_2793_ = v_k_2802_;
goto _start;
}
else
{
lean_dec_ref(v_k_2802_);
lean_dec_ref(v_f_2792_);
return v___x_2803_;
}
}
case 3:
{
lean_object* v_fvarId_2805_; lean_object* v_args_2806_; lean_object* v___x_2807_; 
v_fvarId_2805_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2805_);
v_args_2806_ = lean_ctor_get(v_c_2793_, 1);
lean_inc_ref(v_args_2806_);
lean_dec_ref_known(v_c_2793_, 2);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2807_ = lean_apply_8(v_f_2792_, v_fvarId_2805_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2821_; 
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v___x_2807_, 0);
lean_dec(v_unused_2822_);
v___x_2809_ = v___x_2807_;
v_isShared_2810_ = v_isSharedCheck_2821_;
goto v_resetjp_2808_;
}
else
{
lean_dec(v___x_2807_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2821_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = lean_array_get_size(v_args_2806_);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_nat_dec_lt(v___x_2811_, v___x_2812_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2816_; 
lean_dec_ref(v_args_2806_);
lean_dec_ref(v_f_2792_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2813_);
v___x_2816_ = v___x_2809_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2813_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
else
{
size_t v___x_2818_; size_t v___x_2819_; lean_object* v___x_2820_; 
lean_del_object(v___x_2809_);
v___x_2818_ = ((size_t)0ULL);
v___x_2819_ = lean_usize_of_nat(v___x_2812_);
v___x_2820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2791_, v_f_2792_, v_args_2806_, v___x_2818_, v___x_2819_, v___x_2813_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec_ref(v_args_2806_);
return v___x_2820_;
}
}
}
else
{
lean_dec_ref(v_args_2806_);
lean_dec_ref(v_f_2792_);
return v___x_2807_;
}
}
case 4:
{
lean_object* v_cases_2823_; lean_object* v_resultType_2824_; lean_object* v_discr_2825_; lean_object* v_alts_2826_; lean_object* v___x_2827_; 
v_cases_2823_ = lean_ctor_get(v_c_2793_, 0);
lean_inc_ref(v_cases_2823_);
lean_dec_ref_known(v_c_2793_, 1);
v_resultType_2824_ = lean_ctor_get(v_cases_2823_, 1);
lean_inc_ref(v_resultType_2824_);
v_discr_2825_ = lean_ctor_get(v_cases_2823_, 2);
lean_inc(v_discr_2825_);
v_alts_2826_ = lean_ctor_get(v_cases_2823_, 3);
lean_inc_ref(v_alts_2826_);
lean_dec_ref(v_cases_2823_);
lean_inc_ref(v_f_2792_);
v___x_2827_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2792_, v_resultType_2824_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2828_; 
lean_dec_ref_known(v___x_2827_, 1);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2828_ = lean_apply_8(v_f_2792_, v_discr_2825_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2842_; 
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2843_);
v___x_2830_ = v___x_2828_;
v_isShared_2831_ = v_isSharedCheck_2842_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v___x_2828_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2842_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = lean_array_get_size(v_alts_2826_);
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_nat_dec_lt(v___x_2832_, v___x_2833_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2837_; 
lean_dec_ref(v_alts_2826_);
lean_dec_ref(v_f_2792_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2834_);
v___x_2837_ = v___x_2830_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2834_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
else
{
size_t v___x_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2830_);
v___x_2839_ = ((size_t)0ULL);
v___x_2840_ = lean_usize_of_nat(v___x_2833_);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2791_, v_f_2792_, v_alts_2826_, v___x_2839_, v___x_2840_, v___x_2834_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec_ref(v_alts_2826_);
return v___x_2841_;
}
}
}
else
{
lean_dec_ref(v_alts_2826_);
lean_dec_ref(v_f_2792_);
return v___x_2828_;
}
}
else
{
lean_dec_ref(v_alts_2826_);
lean_dec(v_discr_2825_);
lean_dec_ref(v_f_2792_);
return v___x_2827_;
}
}
case 5:
{
lean_object* v_fvarId_2844_; lean_object* v___x_2845_; 
v_fvarId_2844_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2844_);
lean_dec_ref_known(v_c_2793_, 1);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2845_ = lean_apply_8(v_f_2792_, v_fvarId_2844_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
return v___x_2845_;
}
case 6:
{
lean_object* v_type_2846_; lean_object* v___x_2847_; 
v_type_2846_ = lean_ctor_get(v_c_2793_, 0);
lean_inc_ref(v_type_2846_);
lean_dec_ref_known(v_c_2793_, 1);
v___x_2847_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2792_, v_type_2846_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2847_;
}
case 7:
{
lean_object* v_fvarId_2848_; lean_object* v_y_2849_; lean_object* v_k_2850_; lean_object* v___x_2851_; 
v_fvarId_2848_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2848_);
v_y_2849_ = lean_ctor_get(v_c_2793_, 2);
lean_inc(v_y_2849_);
v_k_2850_ = lean_ctor_get(v_c_2793_, 3);
lean_inc_ref(v_k_2850_);
lean_dec_ref_known(v_c_2793_, 4);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2851_ = lean_apply_8(v_f_2792_, v_fvarId_2848_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; 
lean_dec_ref_known(v___x_2851_, 1);
lean_inc_ref(v_f_2792_);
v___x_2852_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2792_, v_y_2849_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_dec_ref_known(v___x_2852_, 1);
v_c_2793_ = v_k_2850_;
goto _start;
}
else
{
lean_dec_ref(v_k_2850_);
lean_dec_ref(v_f_2792_);
return v___x_2852_;
}
}
else
{
lean_dec_ref(v_k_2850_);
lean_dec(v_y_2849_);
lean_dec_ref(v_f_2792_);
return v___x_2851_;
}
}
case 8:
{
lean_object* v_fvarId_2854_; lean_object* v_y_2855_; lean_object* v_k_2856_; lean_object* v___x_2857_; 
v_fvarId_2854_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2854_);
v_y_2855_ = lean_ctor_get(v_c_2793_, 2);
lean_inc(v_y_2855_);
v_k_2856_ = lean_ctor_get(v_c_2793_, 3);
lean_inc_ref(v_k_2856_);
lean_dec_ref_known(v_c_2793_, 4);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2857_ = lean_apply_8(v_f_2792_, v_fvarId_2854_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref_known(v___x_2857_, 1);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2858_ = lean_apply_8(v_f_2792_, v_y_2855_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_dec_ref_known(v___x_2858_, 1);
v_c_2793_ = v_k_2856_;
goto _start;
}
else
{
lean_dec_ref(v_k_2856_);
lean_dec_ref(v_f_2792_);
return v___x_2858_;
}
}
else
{
lean_dec_ref(v_k_2856_);
lean_dec(v_y_2855_);
lean_dec_ref(v_f_2792_);
return v___x_2857_;
}
}
case 9:
{
lean_object* v_fvarId_2860_; lean_object* v_y_2861_; lean_object* v_ty_2862_; lean_object* v_k_2863_; lean_object* v___x_2864_; 
v_fvarId_2860_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2860_);
v_y_2861_ = lean_ctor_get(v_c_2793_, 3);
lean_inc(v_y_2861_);
v_ty_2862_ = lean_ctor_get(v_c_2793_, 4);
lean_inc_ref(v_ty_2862_);
v_k_2863_ = lean_ctor_get(v_c_2793_, 5);
lean_inc_ref(v_k_2863_);
lean_dec_ref_known(v_c_2793_, 6);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2864_ = lean_apply_8(v_f_2792_, v_fvarId_2860_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v___x_2865_; 
lean_dec_ref_known(v___x_2864_, 1);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2865_ = lean_apply_8(v_f_2792_, v_y_2861_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v___x_2866_; 
lean_dec_ref_known(v___x_2865_, 1);
lean_inc_ref(v_f_2792_);
v___x_2866_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2792_, v_ty_2862_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_dec_ref_known(v___x_2866_, 1);
v_c_2793_ = v_k_2863_;
goto _start;
}
else
{
lean_dec_ref(v_k_2863_);
lean_dec_ref(v_f_2792_);
return v___x_2866_;
}
}
else
{
lean_dec_ref(v_k_2863_);
lean_dec_ref(v_ty_2862_);
lean_dec_ref(v_f_2792_);
return v___x_2865_;
}
}
else
{
lean_dec_ref(v_k_2863_);
lean_dec_ref(v_ty_2862_);
lean_dec(v_y_2861_);
lean_dec_ref(v_f_2792_);
return v___x_2864_;
}
}
case 10:
{
lean_object* v_fvarId_2868_; lean_object* v_k_2869_; lean_object* v___x_2870_; 
v_fvarId_2868_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2868_);
v_k_2869_ = lean_ctor_get(v_c_2793_, 2);
lean_inc_ref(v_k_2869_);
lean_dec_ref_known(v_c_2793_, 3);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2870_ = lean_apply_8(v_f_2792_, v_fvarId_2868_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref_known(v___x_2870_, 1);
v_c_2793_ = v_k_2869_;
goto _start;
}
else
{
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_f_2792_);
return v___x_2870_;
}
}
case 11:
{
lean_object* v_fvarId_2872_; lean_object* v_k_2873_; lean_object* v___x_2874_; 
v_fvarId_2872_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2872_);
v_k_2873_ = lean_ctor_get(v_c_2793_, 2);
lean_inc_ref(v_k_2873_);
lean_dec_ref_known(v_c_2793_, 3);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2874_ = lean_apply_8(v_f_2792_, v_fvarId_2872_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_dec_ref_known(v___x_2874_, 1);
v_c_2793_ = v_k_2873_;
goto _start;
}
else
{
lean_dec_ref(v_k_2873_);
lean_dec_ref(v_f_2792_);
return v___x_2874_;
}
}
case 12:
{
lean_object* v_fvarId_2876_; lean_object* v_k_2877_; lean_object* v___x_2878_; 
v_fvarId_2876_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2876_);
v_k_2877_ = lean_ctor_get(v_c_2793_, 3);
lean_inc_ref(v_k_2877_);
lean_dec_ref_known(v_c_2793_, 4);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2878_ = lean_apply_8(v_f_2792_, v_fvarId_2876_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_dec_ref_known(v___x_2878_, 1);
v_c_2793_ = v_k_2877_;
goto _start;
}
else
{
lean_dec_ref(v_k_2877_);
lean_dec_ref(v_f_2792_);
return v___x_2878_;
}
}
case 13:
{
lean_object* v_fvarId_2880_; lean_object* v_k_2881_; lean_object* v___x_2882_; 
v_fvarId_2880_ = lean_ctor_get(v_c_2793_, 0);
lean_inc(v_fvarId_2880_);
v_k_2881_ = lean_ctor_get(v_c_2793_, 1);
lean_inc_ref(v_k_2881_);
lean_dec_ref_known(v_c_2793_, 2);
lean_inc_ref(v_f_2792_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2882_ = lean_apply_8(v_f_2792_, v_fvarId_2880_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, lean_box(0));
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_dec_ref_known(v___x_2882_, 1);
v_c_2793_ = v_k_2881_;
goto _start;
}
else
{
lean_dec_ref(v_k_2881_);
lean_dec_ref(v_f_2792_);
return v___x_2882_;
}
}
default: 
{
lean_object* v_decl_2884_; lean_object* v_k_2885_; lean_object* v_params_2886_; lean_object* v_type_2887_; lean_object* v_value_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_decl_2884_ = lean_ctor_get(v_c_2793_, 0);
lean_inc_ref(v_decl_2884_);
v_k_2885_ = lean_ctor_get(v_c_2793_, 1);
lean_inc_ref(v_k_2885_);
lean_dec_ref(v_c_2793_);
v_params_2886_ = lean_ctor_get(v_decl_2884_, 2);
lean_inc_ref(v_params_2886_);
v_type_2887_ = lean_ctor_get(v_decl_2884_, 3);
lean_inc_ref(v_type_2887_);
v_value_2888_ = lean_ctor_get(v_decl_2884_, 4);
lean_inc_ref(v_value_2888_);
lean_dec_ref(v_decl_2884_);
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = lean_array_get_size(v_params_2886_);
v___x_2891_ = lean_nat_dec_lt(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec_ref(v_params_2886_);
lean_inc_ref(v_f_2792_);
v___x_2892_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2792_, v_type_2887_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2893_; 
lean_dec_ref_known(v___x_2892_, 1);
lean_inc_ref(v_f_2792_);
v___x_2893_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2791_, v_f_2792_, v_value_2888_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_dec_ref_known(v___x_2893_, 1);
v_c_2793_ = v_k_2885_;
goto _start;
}
else
{
lean_dec_ref(v_k_2885_);
lean_dec_ref(v_f_2792_);
return v___x_2893_;
}
}
else
{
lean_dec_ref(v_value_2888_);
lean_dec_ref(v_k_2885_);
lean_dec_ref(v_f_2792_);
return v___x_2892_;
}
}
else
{
lean_object* v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = ((size_t)0ULL);
v___x_2897_ = lean_usize_of_nat(v___x_2890_);
lean_inc_ref(v_f_2792_);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2791_, v_f_2792_, v_params_2886_, v___x_2896_, v___x_2897_, v___x_2895_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec_ref(v_params_2886_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref_known(v___x_2898_, 1);
lean_inc_ref(v_f_2792_);
v___x_2899_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2792_, v_type_2887_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2900_; 
lean_dec_ref_known(v___x_2899_, 1);
lean_inc_ref(v_f_2792_);
v___x_2900_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2791_, v_f_2792_, v_value_2888_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_dec_ref_known(v___x_2900_, 1);
v_c_2793_ = v_k_2885_;
goto _start;
}
else
{
lean_dec_ref(v_k_2885_);
lean_dec_ref(v_f_2792_);
return v___x_2900_;
}
}
else
{
lean_dec_ref(v_value_2888_);
lean_dec_ref(v_k_2885_);
lean_dec_ref(v_f_2792_);
return v___x_2899_;
}
}
else
{
lean_dec_ref(v_value_2888_);
lean_dec_ref(v_type_2887_);
lean_dec_ref(v_k_2885_);
lean_dec_ref(v_f_2792_);
return v___x_2898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2902_, lean_object* v_f_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2902_, v_f_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_2913_, lean_object* v_f_2914_, lean_object* v_as_2915_, lean_object* v_i_2916_, lean_object* v_stop_2917_, lean_object* v_b_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
uint8_t v_pu_boxed_2926_; size_t v_i_boxed_2927_; size_t v_stop_boxed_2928_; lean_object* v_res_2929_; 
v_pu_boxed_2926_ = lean_unbox(v_pu_2913_);
v_i_boxed_2927_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_stop_boxed_2928_ = lean_unbox_usize(v_stop_2917_);
lean_dec(v_stop_2917_);
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_2926_, v_f_2914_, v_as_2915_, v_i_boxed_2927_, v_stop_boxed_2928_, v_b_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v_as_2915_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_2930_, lean_object* v_f_2931_, lean_object* v_c_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v_pu_boxed_2940_; lean_object* v_res_2941_; 
v_pu_boxed_2940_ = lean_unbox(v_pu_2930_);
v_res_2941_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_2940_, v_f_2931_, v_c_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_2942_, lean_object* v_f_2943_, lean_object* v_decl_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_params_2952_; lean_object* v_type_2953_; lean_object* v_value_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v_params_2952_ = lean_ctor_get(v_decl_2944_, 2);
lean_inc_ref(v_params_2952_);
v_type_2953_ = lean_ctor_get(v_decl_2944_, 3);
lean_inc_ref(v_type_2953_);
v_value_2954_ = lean_ctor_get(v_decl_2944_, 4);
lean_inc_ref(v_value_2954_);
lean_dec_ref(v_decl_2944_);
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = lean_array_get_size(v_params_2952_);
v___x_2957_ = lean_nat_dec_lt(v___x_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec_ref(v_params_2952_);
lean_inc_ref(v_f_2943_);
v___x_2958_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2943_, v_type_2953_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2959_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2942_, v_f_2943_, v_value_2954_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2959_;
}
else
{
lean_dec_ref(v_value_2954_);
lean_dec_ref(v_f_2943_);
return v___x_2958_;
}
}
else
{
lean_object* v___x_2960_; size_t v___x_2961_; size_t v___x_2962_; lean_object* v___x_2963_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = ((size_t)0ULL);
v___x_2962_ = lean_usize_of_nat(v___x_2956_);
lean_inc_ref(v_f_2943_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2942_, v_f_2943_, v_params_2952_, v___x_2961_, v___x_2962_, v___x_2960_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec_ref(v_params_2952_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; 
lean_dec_ref_known(v___x_2963_, 1);
lean_inc_ref(v_f_2943_);
v___x_2964_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2943_, v_type_2953_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2964_, 1);
v___x_2965_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2942_, v_f_2943_, v_value_2954_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
return v___x_2965_;
}
else
{
lean_dec_ref(v_value_2954_);
lean_dec_ref(v_f_2943_);
return v___x_2964_;
}
}
else
{
lean_dec_ref(v_value_2954_);
lean_dec_ref(v_type_2953_);
lean_dec_ref(v_f_2943_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_2966_, lean_object* v_f_2967_, lean_object* v_decl_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v_pu_boxed_2976_; lean_object* v_res_2977_; 
v_pu_boxed_2976_ = lean_unbox(v_pu_2966_);
v_res_2977_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_2976_, v_f_2967_, v_decl_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec(v___y_2969_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_2978_){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_panic_fn_borrowed(v___x_2979_, v_msg_2978_);
return v___x_2980_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2984_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_2985_ = lean_unsigned_to_nat(11u);
v___x_2986_ = lean_unsigned_to_nat(163u);
v___x_2987_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_2988_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_2989_ = l_mkPanicMessageWithDecl(v___x_2988_, v___x_2987_, v___x_2986_, v___x_2985_, v___x_2984_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_2990_, lean_object* v_x_2991_){
_start:
{
if (lean_obj_tag(v_x_2991_) == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_2993_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_2992_);
return v___x_2993_;
}
else
{
lean_object* v_key_2994_; lean_object* v_value_2995_; lean_object* v_tail_2996_; uint8_t v___x_2997_; 
v_key_2994_ = lean_ctor_get(v_x_2991_, 0);
v_value_2995_ = lean_ctor_get(v_x_2991_, 1);
v_tail_2996_ = lean_ctor_get(v_x_2991_, 2);
v___x_2997_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2994_, v_a_2990_);
if (v___x_2997_ == 0)
{
v_x_2991_ = v_tail_2996_;
goto _start;
}
else
{
lean_inc(v_value_2995_);
return v_value_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_2999_, v_x_3000_);
lean_dec(v_x_3000_);
lean_dec(v_a_2999_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_buckets_3004_; lean_object* v___x_3005_; uint64_t v___x_3006_; uint64_t v___x_3007_; uint64_t v___x_3008_; uint64_t v_fold_3009_; uint64_t v___x_3010_; uint64_t v___x_3011_; uint64_t v___x_3012_; size_t v___x_3013_; size_t v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_buckets_3004_ = lean_ctor_get(v_m_3002_, 1);
v___x_3005_ = lean_array_get_size(v_buckets_3004_);
v___x_3006_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_3003_);
v___x_3007_ = 32ULL;
v___x_3008_ = lean_uint64_shift_right(v___x_3006_, v___x_3007_);
v_fold_3009_ = lean_uint64_xor(v___x_3006_, v___x_3008_);
v___x_3010_ = 16ULL;
v___x_3011_ = lean_uint64_shift_right(v_fold_3009_, v___x_3010_);
v___x_3012_ = lean_uint64_xor(v_fold_3009_, v___x_3011_);
v___x_3013_ = lean_uint64_to_usize(v___x_3012_);
v___x_3014_ = lean_usize_of_nat(v___x_3005_);
v___x_3015_ = ((size_t)1ULL);
v___x_3016_ = lean_usize_sub(v___x_3014_, v___x_3015_);
v___x_3017_ = lean_usize_land(v___x_3013_, v___x_3016_);
v___x_3018_ = lean_array_uget_borrowed(v_buckets_3004_, v___x_3017_);
v___x_3019_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3003_, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3020_, v_a_3021_);
lean_dec(v_a_3021_);
lean_dec_ref(v_m_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v___y_3033_; uint8_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = 0;
v___x_3059_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3024_))
{
case 0:
{
lean_object* v_decl_3060_; lean_object* v___x_3061_; 
v_decl_3060_ = lean_ctor_get(v_decl_3024_, 0);
lean_inc_ref(v_decl_3060_);
v___x_3061_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3058_, v___x_3059_, v_decl_3060_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
v___y_3033_ = v___x_3061_;
goto v___jp_3032_;
}
case 1:
{
lean_object* v_decl_3062_; lean_object* v___x_3063_; 
v_decl_3062_ = lean_ctor_get(v_decl_3024_, 0);
lean_inc_ref(v_decl_3062_);
v___x_3063_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3058_, v___x_3059_, v_decl_3062_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
v___y_3033_ = v___x_3063_;
goto v___jp_3032_;
}
case 2:
{
lean_object* v_decl_3064_; lean_object* v___x_3065_; 
v_decl_3064_ = lean_ctor_get(v_decl_3024_, 0);
lean_inc_ref(v_decl_3064_);
v___x_3065_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3058_, v___x_3059_, v_decl_3064_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
v___y_3033_ = v___x_3065_;
goto v___jp_3032_;
}
case 3:
{
lean_object* v_fvarId_3066_; lean_object* v_y_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_fvarId_3066_ = lean_ctor_get(v_decl_3024_, 0);
v_y_3067_ = lean_ctor_get(v_decl_3024_, 2);
lean_inc(v_fvarId_3066_);
v___x_3068_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3066_, v_a_3025_);
lean_dec_ref(v___x_3068_);
lean_inc(v_y_3067_);
v___x_3069_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3059_, v_y_3067_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
v___y_3033_ = v___x_3069_;
goto v___jp_3032_;
}
case 4:
{
lean_object* v_fvarId_3070_; lean_object* v_y_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_fvarId_3070_ = lean_ctor_get(v_decl_3024_, 0);
v_y_3071_ = lean_ctor_get(v_decl_3024_, 2);
lean_inc(v_fvarId_3070_);
v___x_3072_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3070_, v_a_3025_);
lean_dec_ref(v___x_3072_);
lean_inc(v_y_3071_);
v___x_3073_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3071_, v_a_3025_);
v___y_3033_ = v___x_3073_;
goto v___jp_3032_;
}
case 5:
{
lean_object* v_fvarId_3074_; lean_object* v_y_3075_; lean_object* v_ty_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_fvarId_3074_ = lean_ctor_get(v_decl_3024_, 0);
v_y_3075_ = lean_ctor_get(v_decl_3024_, 3);
v_ty_3076_ = lean_ctor_get(v_decl_3024_, 4);
lean_inc(v_fvarId_3074_);
v___x_3077_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3074_, v_a_3025_);
lean_dec_ref(v___x_3077_);
lean_inc(v_y_3075_);
v___x_3078_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3075_, v_a_3025_);
lean_dec_ref(v___x_3078_);
lean_inc_ref(v_ty_3076_);
v___x_3079_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3059_, v_ty_3076_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
v___y_3033_ = v___x_3079_;
goto v___jp_3032_;
}
default: 
{
lean_object* v_fvarId_3080_; lean_object* v___x_3081_; 
v_fvarId_3080_ = lean_ctor_get(v_decl_3024_, 0);
lean_inc(v_fvarId_3080_);
v___x_3081_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3080_, v_a_3025_);
v___y_3033_ = v___x_3081_;
goto v___jp_3032_;
}
}
v___jp_3032_:
{
if (lean_obj_tag(v___y_3033_) == 0)
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v___y_3033_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___y_3033_, 0);
lean_dec(v_unused_3057_);
v___x_3035_ = v___y_3033_;
v_isShared_3036_ = v_isSharedCheck_3056_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v___y_3033_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3056_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v_decision_3038_; lean_object* v_newArms_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3055_; 
v___x_3037_ = lean_st_ref_take(v_a_3025_);
v_decision_3038_ = lean_ctor_get(v___x_3037_, 0);
v_newArms_3039_ = lean_ctor_get(v___x_3037_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3041_ = v___x_3037_;
v_isShared_3042_ = v_isSharedCheck_3055_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_newArms_3039_);
lean_inc(v_decision_3038_);
lean_dec(v___x_3037_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3055_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3043_ = lean_box(2);
v___x_3044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3039_, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_decl_3024_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3039_, v___x_3043_, v___x_3045_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 1, v___x_3046_);
v___x_3048_ = v___x_3041_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_decision_3038_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3049_ = lean_st_ref_put(v_a_3025_, v___x_3048_);
v___x_3050_ = lean_box(0);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3050_);
v___x_3052_ = v___x_3035_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3024_);
return v___y_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec(v_a_3083_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3091_, lean_object* v_f_3092_, lean_object* v_arg_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3092_, v_arg_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3102_, lean_object* v_f_3103_, lean_object* v_arg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
uint8_t v_pu_boxed_3112_; lean_object* v_res_3113_; 
v_pu_boxed_3112_ = lean_unbox(v_pu_3102_);
v_res_3113_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3112_, v_f_3103_, v_arg_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec(v___y_3105_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3114_, lean_object* v_f_3115_, lean_object* v_param_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3115_, v_param_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3125_, lean_object* v_f_3126_, lean_object* v_param_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v_pu_boxed_3135_; lean_object* v_res_3136_; 
v_pu_boxed_3135_ = lean_unbox(v_pu_3125_);
v_res_3136_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3135_, v_f_3126_, v_param_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec(v___y_3128_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3137_, lean_object* v_alt_3138_, lean_object* v_f_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3138_, v_f_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3148_, lean_object* v_alt_3149_, lean_object* v_f_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
uint8_t v_pu_boxed_3158_; lean_object* v_res_3159_; 
v_pu_boxed_3158_ = lean_unbox(v_pu_3148_);
v_res_3159_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3158_, v_alt_3149_, v_f_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3160_, lean_object* v_arm_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v___x_3164_; lean_object* v_decision_3181_; lean_object* v___x_3182_; 
v___x_3164_ = lean_st_ref_get(v_a_3162_);
v_decision_3181_ = lean_ctor_get(v___x_3164_, 0);
lean_inc_ref(v_decision_3181_);
lean_dec(v___x_3164_);
v___x_3182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3181_, v_fvar_3160_);
lean_dec_ref(v_decision_3181_);
if (lean_obj_tag(v___x_3182_) == 1)
{
lean_object* v_val_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3210_; 
v_val_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3210_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_val_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3210_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = lean_box(3);
v___x_3188_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3183_, v___x_3187_);
if (v___x_3188_ == 0)
{
uint8_t v___x_3189_; 
v___x_3189_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3183_, v_arm_3161_);
lean_dec(v_arm_3161_);
lean_dec(v_val_3183_);
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3185_);
goto v___jp_3165_;
}
else
{
if (v___x_3188_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
lean_dec(v_fvar_3160_);
v___x_3190_ = lean_box(0);
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3190_);
v___x_3192_ = v___x_3185_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
else
{
lean_del_object(v___x_3185_);
goto v___jp_3165_;
}
}
}
else
{
lean_object* v___x_3194_; lean_object* v_decision_3195_; lean_object* v_newArms_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_val_3183_);
v___x_3194_ = lean_st_ref_take(v_a_3162_);
v_decision_3195_ = lean_ctor_get(v___x_3194_, 0);
v_newArms_3196_ = lean_ctor_get(v___x_3194_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3198_ = v___x_3194_;
v_isShared_3199_ = v_isSharedCheck_3209_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_newArms_3196_);
lean_inc(v_decision_3195_);
lean_dec(v___x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3209_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3195_, v_fvar_3160_, v_arm_3161_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3200_);
v___x_3202_ = v___x_3198_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_newArms_3196_);
v___x_3202_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3203_ = lean_st_ref_put(v_a_3162_, v___x_3202_);
v___x_3204_ = lean_box(0);
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3204_);
v___x_3206_ = v___x_3185_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec(v___x_3182_);
lean_dec(v_arm_3161_);
lean_dec(v_fvar_3160_);
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
v___jp_3165_:
{
lean_object* v___x_3166_; lean_object* v_decision_3167_; lean_object* v_newArms_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3180_; 
v___x_3166_ = lean_st_ref_take(v_a_3162_);
v_decision_3167_ = lean_ctor_get(v___x_3166_, 0);
v_newArms_3168_ = lean_ctor_get(v___x_3166_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3170_ = v___x_3166_;
v_isShared_3171_ = v_isSharedCheck_3180_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_newArms_3168_);
lean_inc(v_decision_3167_);
lean_dec(v___x_3166_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3180_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3172_ = lean_box(2);
v___x_3173_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3167_, v_fvar_3160_, v___x_3172_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3173_);
v___x_3175_ = v___x_3170_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_newArms_3168_);
v___x_3175_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = lean_st_ref_put(v_a_3162_, v___x_3175_);
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3213_, lean_object* v_arm_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3213_, v_arm_3214_, v_a_3215_);
lean_dec(v_a_3215_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3218_, lean_object* v_arm_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3218_, v_arm_3219_, v_a_3220_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3228_, lean_object* v_arm_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3228_, v_arm_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec(v_a_3230_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3239_, v___x_3238_, v___y_3240_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3248_, lean_object* v_x_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3248_, v_x_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3258_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3260_ = lean_panic_fn_borrowed(v___x_3259_, v_msg_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3261_, lean_object* v_x_3262_){
_start:
{
if (lean_obj_tag(v_x_3262_) == 0)
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3264_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3263_);
return v___x_3264_;
}
else
{
lean_object* v_key_3265_; lean_object* v_value_3266_; lean_object* v_tail_3267_; uint8_t v___x_3268_; 
v_key_3265_ = lean_ctor_get(v_x_3262_, 0);
v_value_3266_ = lean_ctor_get(v_x_3262_, 1);
v_tail_3267_ = lean_ctor_get(v_x_3262_, 2);
v___x_3268_ = l_Lean_instBEqFVarId_beq(v_key_3265_, v_a_3261_);
if (v___x_3268_ == 0)
{
v_x_3262_ = v_tail_3267_;
goto _start;
}
else
{
lean_inc(v_value_3266_);
return v_value_3266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3270_, v_x_3271_);
lean_dec(v_x_3271_);
lean_dec(v_a_3270_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v_buckets_3275_; lean_object* v___x_3276_; uint64_t v___x_3277_; uint64_t v___x_3278_; uint64_t v___x_3279_; uint64_t v_fold_3280_; uint64_t v___x_3281_; uint64_t v___x_3282_; uint64_t v___x_3283_; size_t v___x_3284_; size_t v___x_3285_; size_t v___x_3286_; size_t v___x_3287_; size_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_buckets_3275_ = lean_ctor_get(v_m_3273_, 1);
v___x_3276_ = lean_array_get_size(v_buckets_3275_);
v___x_3277_ = l_Lean_instHashableFVarId_hash(v_a_3274_);
v___x_3278_ = 32ULL;
v___x_3279_ = lean_uint64_shift_right(v___x_3277_, v___x_3278_);
v_fold_3280_ = lean_uint64_xor(v___x_3277_, v___x_3279_);
v___x_3281_ = 16ULL;
v___x_3282_ = lean_uint64_shift_right(v_fold_3280_, v___x_3281_);
v___x_3283_ = lean_uint64_xor(v_fold_3280_, v___x_3282_);
v___x_3284_ = lean_uint64_to_usize(v___x_3283_);
v___x_3285_ = lean_usize_of_nat(v___x_3276_);
v___x_3286_ = ((size_t)1ULL);
v___x_3287_ = lean_usize_sub(v___x_3285_, v___x_3286_);
v___x_3288_ = lean_usize_land(v___x_3284_, v___x_3287_);
v___x_3289_ = lean_array_uget_borrowed(v_buckets_3275_, v___x_3288_);
v___x_3290_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3274_, v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_m_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v___x_3302_; lean_object* v_decision_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3360_; 
v___x_3302_ = lean_st_ref_get(v_a_3295_);
v_decision_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; 
v_unused_3361_ = lean_ctor_get(v___x_3302_, 1);
lean_dec(v_unused_3361_);
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3360_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_decision_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3360_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
uint8_t v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___y_3311_; lean_object* v___f_3337_; 
v___x_3307_ = 0;
v___x_3308_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3294_);
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3303_, v___x_3308_);
lean_dec(v___x_3308_);
lean_dec_ref(v_decision_3303_);
lean_inc(v___x_3309_);
v___f_3337_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3337_, 0, v___x_3309_);
switch(lean_obj_tag(v_decl_3294_))
{
case 0:
{
lean_object* v_decl_3338_; lean_object* v___x_3339_; 
v_decl_3338_ = lean_ctor_get(v_decl_3294_, 0);
lean_inc_ref(v_decl_3338_);
v___x_3339_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3307_, v___f_3337_, v_decl_3338_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
v___y_3311_ = v___x_3339_;
goto v___jp_3310_;
}
case 1:
{
lean_object* v_decl_3340_; lean_object* v___x_3341_; 
v_decl_3340_ = lean_ctor_get(v_decl_3294_, 0);
lean_inc_ref(v_decl_3340_);
v___x_3341_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3307_, v___f_3337_, v_decl_3340_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
v___y_3311_ = v___x_3341_;
goto v___jp_3310_;
}
case 2:
{
lean_object* v_decl_3342_; lean_object* v___x_3343_; 
v_decl_3342_ = lean_ctor_get(v_decl_3294_, 0);
lean_inc_ref(v_decl_3342_);
v___x_3343_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3307_, v___f_3337_, v_decl_3342_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
v___y_3311_ = v___x_3343_;
goto v___jp_3310_;
}
case 3:
{
lean_object* v_fvarId_3344_; lean_object* v_y_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_fvarId_3344_ = lean_ctor_get(v_decl_3294_, 0);
v_y_3345_ = lean_ctor_get(v_decl_3294_, 2);
lean_inc(v___x_3309_);
lean_inc(v_fvarId_3344_);
v___x_3346_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3344_, v___x_3309_, v_a_3295_);
lean_dec_ref(v___x_3346_);
lean_inc(v_y_3345_);
v___x_3347_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3337_, v_y_3345_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
v___y_3311_ = v___x_3347_;
goto v___jp_3310_;
}
case 4:
{
lean_object* v_fvarId_3348_; lean_object* v_y_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref(v___f_3337_);
v_fvarId_3348_ = lean_ctor_get(v_decl_3294_, 0);
v_y_3349_ = lean_ctor_get(v_decl_3294_, 2);
lean_inc_n(v___x_3309_, 2);
lean_inc(v_fvarId_3348_);
v___x_3350_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3348_, v___x_3309_, v_a_3295_);
lean_dec_ref(v___x_3350_);
lean_inc(v_y_3349_);
v___x_3351_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3349_, v___x_3309_, v_a_3295_);
v___y_3311_ = v___x_3351_;
goto v___jp_3310_;
}
case 5:
{
lean_object* v_fvarId_3352_; lean_object* v_y_3353_; lean_object* v_ty_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_fvarId_3352_ = lean_ctor_get(v_decl_3294_, 0);
v_y_3353_ = lean_ctor_get(v_decl_3294_, 3);
v_ty_3354_ = lean_ctor_get(v_decl_3294_, 4);
lean_inc_n(v___x_3309_, 2);
lean_inc(v_fvarId_3352_);
v___x_3355_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3352_, v___x_3309_, v_a_3295_);
lean_dec_ref(v___x_3355_);
lean_inc(v_y_3353_);
v___x_3356_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3353_, v___x_3309_, v_a_3295_);
lean_dec_ref(v___x_3356_);
lean_inc_ref(v_ty_3354_);
v___x_3357_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3337_, v_ty_3354_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
v___y_3311_ = v___x_3357_;
goto v___jp_3310_;
}
default: 
{
lean_object* v_fvarId_3358_; lean_object* v___x_3359_; 
lean_dec_ref(v___f_3337_);
v_fvarId_3358_ = lean_ctor_get(v_decl_3294_, 0);
lean_inc(v___x_3309_);
lean_inc(v_fvarId_3358_);
v___x_3359_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3358_, v___x_3309_, v_a_3295_);
v___y_3311_ = v___x_3359_;
goto v___jp_3310_;
}
}
v___jp_3310_:
{
if (lean_obj_tag(v___y_3311_) == 0)
{
lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3335_; 
v_isSharedCheck_3335_ = !lean_is_exclusive(v___y_3311_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v___y_3311_, 0);
lean_dec(v_unused_3336_);
v___x_3313_ = v___y_3311_;
v_isShared_3314_ = v_isSharedCheck_3335_;
goto v_resetjp_3312_;
}
else
{
lean_dec(v___y_3311_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3335_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v_decision_3316_; lean_object* v_newArms_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3334_; 
v___x_3315_ = lean_st_ref_take(v_a_3295_);
v_decision_3316_ = lean_ctor_get(v___x_3315_, 0);
v_newArms_3317_ = lean_ctor_get(v___x_3315_, 1);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3334_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_newArms_3317_);
lean_inc(v_decision_3316_);
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3334_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
v___x_3321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3317_, v___x_3309_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 1);
lean_ctor_set(v___x_3305_, 1, v___x_3321_);
lean_ctor_set(v___x_3305_, 0, v_decl_3294_);
v___x_3323_ = v___x_3305_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_decl_3294_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3324_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3317_, v___x_3309_, v___x_3323_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v___x_3324_);
v___x_3326_ = v___x_3319_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_decision_3316_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3327_ = lean_st_ref_put(v_a_3295_, v___x_3326_);
v___x_3328_ = lean_box(0);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3328_);
v___x_3330_ = v___x_3313_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3328_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3309_);
lean_del_object(v___x_3305_);
lean_dec_ref(v_decl_3294_);
return v___y_3311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec(v_a_3363_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3371_, lean_object* v_b_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
if (lean_obj_tag(v_as_x27_3371_) == 0)
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_b_3372_);
return v___x_3380_;
}
else
{
lean_object* v_head_3381_; lean_object* v_tail_3382_; lean_object* v___x_3383_; lean_object* v_decision_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_head_3381_ = lean_ctor_get(v_as_x27_3371_, 0);
v_tail_3382_ = lean_ctor_get(v_as_x27_3371_, 1);
v___x_3383_ = lean_st_ref_get(v___y_3373_);
v_decision_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_decision_3384_);
lean_dec(v___x_3383_);
v___x_3385_ = lean_box(0);
v___x_3386_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3381_);
v___x_3387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3384_, v___x_3386_);
lean_dec(v___x_3386_);
lean_dec_ref(v_decision_3384_);
v___x_3388_ = lean_box(3);
v___x_3389_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3387_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3390_ = lean_box(2);
v___x_3391_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3387_, v___x_3390_);
lean_dec(v___x_3387_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_inc(v_head_3381_);
v___x_3392_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3381_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_dec_ref_known(v___x_3392_, 1);
v_as_x27_3371_ = v_tail_3382_;
v_b_3372_ = v___x_3385_;
goto _start;
}
else
{
return v___x_3392_;
}
}
else
{
lean_object* v___x_3394_; 
lean_inc(v_head_3381_);
v___x_3394_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3381_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_dec_ref_known(v___x_3394_, 1);
v_as_x27_3371_ = v_tail_3382_;
v_b_3372_ = v___x_3385_;
goto _start;
}
else
{
return v___x_3394_;
}
}
}
else
{
uint8_t v___x_3396_; lean_object* v___x_3397_; 
lean_dec(v___x_3387_);
v___x_3396_ = 0;
v___x_3397_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3396_, v_head_3381_, v___y_3376_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_dec_ref_known(v___x_3397_, 1);
v_as_x27_3371_ = v_tail_3382_;
v_b_3372_ = v___x_3385_;
goto _start;
}
else
{
return v___x_3397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3399_, lean_object* v_b_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3399_, v_b_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec(v_as_x27_3399_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_box(0);
v___x_3417_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3410_, v___x_3416_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v___x_3417_, 0);
lean_dec(v_unused_3425_);
v___x_3419_ = v___x_3417_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_dec(v___x_3417_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3416_);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3416_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec(v_a_3426_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3434_, lean_object* v_as_x27_3435_, lean_object* v_b_3436_, lean_object* v_a_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3435_, v_b_3436_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_3446_, lean_object* v_as_x27_3447_, lean_object* v_b_3448_, lean_object* v_a_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3446_, v_as_x27_3447_, v_b_3448_, v_a_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v_as_x27_3447_);
lean_dec(v_as_3446_);
return v_res_3457_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3458_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3462_ = lean_unsigned_to_nat(0u);
v___x_3463_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
lean_ctor_set(v___x_3463_, 2, v___x_3462_);
lean_ctor_set(v___x_3463_, 3, v___x_3462_);
lean_ctor_set(v___x_3463_, 4, v___x_3461_);
lean_ctor_set(v___x_3463_, 5, v___x_3461_);
lean_ctor_set(v___x_3463_, 6, v___x_3461_);
lean_ctor_set(v___x_3463_, 7, v___x_3461_);
lean_ctor_set(v___x_3463_, 8, v___x_3461_);
lean_ctor_set(v___x_3463_, 9, v___x_3461_);
lean_ctor_set(v___x_3463_, 10, v___x_3461_);
return v___x_3463_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3464_; double v___x_3465_; 
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_float_of_nat(v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3469_, lean_object* v_msg_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_toCold_3476_; lean_object* v_ref_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v_toCold_3476_ = lean_ctor_get(v___y_3473_, 0);
v_ref_3477_ = lean_ctor_get(v___y_3473_, 2);
v___x_3478_ = lean_st_ref_get(v___y_3474_);
v___x_3479_ = lean_st_ref_get(v___y_3472_);
v___x_3480_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3471_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3540_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3540_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3540_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_env_3485_; lean_object* v_lctx_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3538_; 
v_env_3485_ = lean_ctor_get(v___x_3478_, 0);
lean_inc_ref(v_env_3485_);
lean_dec(v___x_3478_);
v_lctx_3486_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v___x_3479_, 1);
lean_dec(v_unused_3539_);
v___x_3488_ = v___x_3479_;
v_isShared_3489_ = v_isSharedCheck_3538_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_lctx_3486_);
lean_dec(v___x_3479_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3538_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_options_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v_traceState_3493_; lean_object* v_env_3494_; lean_object* v_nextMacroScope_3495_; lean_object* v_ngen_3496_; lean_object* v_auxDeclNGen_3497_; lean_object* v_cache_3498_; lean_object* v_messages_3499_; lean_object* v_infoState_3500_; lean_object* v_snapshotTasks_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3537_; 
v_options_3490_ = lean_ctor_get(v_toCold_3476_, 2);
v___x_3491_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3492_ = lean_st_ref_take(v___y_3474_);
v_traceState_3493_ = lean_ctor_get(v___x_3492_, 4);
v_env_3494_ = lean_ctor_get(v___x_3492_, 0);
v_nextMacroScope_3495_ = lean_ctor_get(v___x_3492_, 1);
v_ngen_3496_ = lean_ctor_get(v___x_3492_, 2);
v_auxDeclNGen_3497_ = lean_ctor_get(v___x_3492_, 3);
v_cache_3498_ = lean_ctor_get(v___x_3492_, 5);
v_messages_3499_ = lean_ctor_get(v___x_3492_, 6);
v_infoState_3500_ = lean_ctor_get(v___x_3492_, 7);
v_snapshotTasks_3501_ = lean_ctor_get(v___x_3492_, 8);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3503_ = v___x_3492_;
v_isShared_3504_ = v_isSharedCheck_3537_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snapshotTasks_3501_);
lean_inc(v_infoState_3500_);
lean_inc(v_messages_3499_);
lean_inc(v_cache_3498_);
lean_inc(v_traceState_3493_);
lean_inc(v_auxDeclNGen_3497_);
lean_inc(v_ngen_3496_);
lean_inc(v_nextMacroScope_3495_);
lean_inc(v_env_3494_);
lean_dec(v___x_3492_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3537_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
uint64_t v_tid_3505_; lean_object* v_traces_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3536_; 
v_tid_3505_ = lean_ctor_get_uint64(v_traceState_3493_, sizeof(void*)*1);
v_traces_3506_ = lean_ctor_get(v_traceState_3493_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_traceState_3493_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3508_ = v_traceState_3493_;
v_isShared_3509_ = v_isSharedCheck_3536_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_traces_3506_);
lean_dec(v_traceState_3493_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3536_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3510_ = lean_unbox(v_a_3481_);
lean_dec(v_a_3481_);
v___x_3511_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3486_, v___x_3510_);
lean_dec_ref(v_lctx_3486_);
lean_inc_ref(v_options_3490_);
v___x_3512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3512_, 0, v_env_3485_);
lean_ctor_set(v___x_3512_, 1, v___x_3491_);
lean_ctor_set(v___x_3512_, 2, v___x_3511_);
lean_ctor_set(v___x_3512_, 3, v_options_3490_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set_tag(v___x_3488_, 3);
lean_ctor_set(v___x_3488_, 1, v_msg_3470_);
lean_ctor_set(v___x_3488_, 0, v___x_3512_);
v___x_3514_ = v___x_3488_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_msg_3470_);
v___x_3514_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; double v___x_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3517_ = 0;
v___x_3518_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3519_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3519_, 0, v_cls_3469_);
lean_ctor_set(v___x_3519_, 1, v___x_3515_);
lean_ctor_set(v___x_3519_, 2, v___x_3518_);
lean_ctor_set_float(v___x_3519_, sizeof(void*)*3, v___x_3516_);
lean_ctor_set_float(v___x_3519_, sizeof(void*)*3 + 8, v___x_3516_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3 + 16, v___x_3517_);
v___x_3520_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3521_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3514_);
lean_ctor_set(v___x_3521_, 2, v___x_3520_);
lean_inc(v_ref_3477_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_ref_3477_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_PersistentArray_push___redArg(v_traces_3506_, v___x_3522_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3523_);
v___x_3525_ = v___x_3508_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3523_);
lean_ctor_set_uint64(v_reuseFailAlloc_3534_, sizeof(void*)*1, v_tid_3505_);
v___x_3525_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3527_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 4, v___x_3525_);
v___x_3527_ = v___x_3503_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_env_3494_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_nextMacroScope_3495_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_ngen_3496_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_auxDeclNGen_3497_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3533_, 5, v_cache_3498_);
lean_ctor_set(v_reuseFailAlloc_3533_, 6, v_messages_3499_);
lean_ctor_set(v_reuseFailAlloc_3533_, 7, v_infoState_3500_);
lean_ctor_set(v_reuseFailAlloc_3533_, 8, v_snapshotTasks_3501_);
v___x_3527_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3528_ = lean_st_ref_put(v___y_3474_, v___x_3527_);
v___x_3529_ = lean_box(0);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3529_);
v___x_3531_ = v___x_3483_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
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
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v___x_3479_);
lean_dec(v___x_3478_);
lean_dec_ref(v_msg_3470_);
lean_dec(v_cls_3469_);
v_a_3541_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3480_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3480_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3549_, lean_object* v_msg_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3549_, v_msg_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3557_, lean_object* v_msg_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3557_, v_msg_3558_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3566_, lean_object* v_msg_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3566_, v_msg_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
return v_res_3574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3584_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3585_ = l_Lean_Name_append(v___x_3584_, v___x_3583_);
return v___x_3585_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3588_ = l_Lean_stringToMessageData(v___x_3587_);
return v___x_3588_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
switch(lean_obj_tag(v_code_3592_))
{
case 0:
{
lean_object* v_decl_3599_; lean_object* v_k_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_decl_3599_ = lean_ctor_get(v_code_3592_, 0);
lean_inc_ref(v_decl_3599_);
v_k_3600_ = lean_ctor_get(v_code_3592_, 1);
lean_inc_ref(v_k_3600_);
lean_dec_ref_known(v_code_3592_, 2);
v___x_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_decl_3599_);
v___x_3602_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3602_, 0, v_k_3600_);
v___x_3603_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3601_, v___x_3602_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3603_;
}
case 1:
{
lean_object* v_decl_3604_; lean_object* v_k_3605_; lean_object* v_params_3606_; lean_object* v_type_3607_; lean_object* v_value_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_decl_3604_ = lean_ctor_get(v_code_3592_, 0);
lean_inc_ref(v_decl_3604_);
v_k_3605_ = lean_ctor_get(v_code_3592_, 1);
lean_inc_ref(v_k_3605_);
lean_dec_ref_known(v_code_3592_, 2);
v_params_3606_ = lean_ctor_get(v_decl_3604_, 2);
lean_inc_ref(v_params_3606_);
v_type_3607_ = lean_ctor_get(v_decl_3604_, 3);
lean_inc_ref(v_type_3607_);
v_value_3608_ = lean_ctor_get(v_decl_3604_, 4);
lean_inc_ref(v_value_3608_);
v___x_3609_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3609_, 0, v_value_3608_);
v___x_3610_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3609_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3631_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3631_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3631_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
uint8_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = 0;
v___x_3616_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3615_, v_decl_3604_, v_type_3607_, v_params_3606_, v_a_3611_, v_a_3595_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 1);
lean_ctor_set(v___x_3613_, 0, v_a_3617_);
v___x_3619_ = v___x_3613_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3617_);
v___x_3619_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3620_, 0, v_k_3605_);
v___x_3621_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3619_, v___x_3620_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3621_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_del_object(v___x_3613_);
lean_dec_ref(v_k_3605_);
v_a_3623_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3616_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3616_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3607_);
lean_dec_ref(v_params_3606_);
lean_dec_ref(v_k_3605_);
lean_dec_ref(v_decl_3604_);
return v___x_3610_;
}
}
case 2:
{
lean_object* v_decl_3632_; lean_object* v_k_3633_; lean_object* v_params_3634_; lean_object* v_type_3635_; lean_object* v_value_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_decl_3632_ = lean_ctor_get(v_code_3592_, 0);
lean_inc_ref(v_decl_3632_);
v_k_3633_ = lean_ctor_get(v_code_3592_, 1);
lean_inc_ref(v_k_3633_);
lean_dec_ref_known(v_code_3592_, 2);
v_params_3634_ = lean_ctor_get(v_decl_3632_, 2);
lean_inc_ref(v_params_3634_);
v_type_3635_ = lean_ctor_get(v_decl_3632_, 3);
lean_inc_ref(v_type_3635_);
v_value_3636_ = lean_ctor_get(v_decl_3632_, 4);
lean_inc_ref(v_value_3636_);
v___x_3637_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3637_, 0, v_value_3636_);
v___x_3638_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3637_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3659_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3659_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3659_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
uint8_t v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = 0;
v___x_3644_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3643_, v_decl_3632_, v_type_3635_, v_params_3634_, v_a_3639_, v_a_3595_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 2);
lean_ctor_set(v___x_3641_, 0, v_a_3645_);
v___x_3647_ = v___x_3641_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3645_);
v___x_3647_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3648_, 0, v_k_3633_);
v___x_3649_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3647_, v___x_3648_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3649_;
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_del_object(v___x_3641_);
lean_dec_ref(v_k_3633_);
v_a_3651_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3644_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3644_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3635_);
lean_dec_ref(v_params_3634_);
lean_dec_ref(v_k_3633_);
lean_dec_ref(v_decl_3632_);
return v___x_3638_;
}
}
case 4:
{
lean_object* v_cases_3660_; lean_object* v___x_3661_; 
v_cases_3660_ = lean_ctor_get(v_code_3592_, 0);
lean_inc_ref_n(v_cases_3660_, 2);
v___x_3661_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3660_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v___x_3663_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3660_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_a_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_st_mk_ref(v___x_3664_);
v___x_3666_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3665_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3667_; lean_object* v_typeName_3668_; lean_object* v_resultType_3669_; lean_object* v_discr_3670_; lean_object* v_alts_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref_known(v___x_3666_, 1);
v___x_3667_ = lean_st_ref_get(v___x_3665_);
lean_dec(v___x_3665_);
v_typeName_3668_ = lean_ctor_get(v_cases_3660_, 0);
v_resultType_3669_ = lean_ctor_get(v_cases_3660_, 1);
v_discr_3670_ = lean_ctor_get(v_cases_3660_, 2);
v_alts_3671_ = lean_ctor_get(v_cases_3660_, 3);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_cases_3660_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3673_ = v_cases_3660_;
v_isShared_3674_ = v_isSharedCheck_3712_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_alts_3671_);
lean_inc(v_discr_3670_);
lean_inc(v_resultType_3669_);
lean_inc(v_typeName_3668_);
lean_dec(v_cases_3660_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3712_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_newArms_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_newArms_3675_ = lean_ctor_get(v___x_3667_, 1);
lean_inc_ref(v_newArms_3675_);
lean_dec(v___x_3667_);
v___x_3676_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3671_);
v___x_3677_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3675_, v___x_3676_, v_alts_3671_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3703_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3703_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3703_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
uint8_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___y_3686_; size_t v___x_3697_; size_t v___x_3698_; uint8_t v___x_3699_; 
v___x_3682_ = 0;
v___x_3683_ = lean_box(2);
v___x_3684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3675_, v___x_3683_);
lean_dec_ref(v_newArms_3675_);
v___x_3697_ = lean_ptr_addr(v_alts_3671_);
lean_dec_ref(v_alts_3671_);
v___x_3698_ = lean_ptr_addr(v_a_3678_);
v___x_3699_ = lean_usize_dec_eq(v___x_3697_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_dec_ref_known(v_code_3592_, 1);
goto v___jp_3692_;
}
else
{
size_t v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = lean_ptr_addr(v_resultType_3669_);
v___x_3701_ = lean_usize_dec_eq(v___x_3700_, v___x_3700_);
if (v___x_3701_ == 0)
{
lean_dec_ref_known(v_code_3592_, 1);
goto v___jp_3692_;
}
else
{
uint8_t v___x_3702_; 
v___x_3702_ = l_Lean_instBEqFVarId_beq(v_discr_3670_, v_discr_3670_);
if (v___x_3702_ == 0)
{
lean_dec_ref_known(v_code_3592_, 1);
goto v___jp_3692_;
}
else
{
lean_dec(v_a_3678_);
lean_del_object(v___x_3673_);
lean_dec(v_discr_3670_);
lean_dec_ref(v_resultType_3669_);
lean_dec(v_typeName_3668_);
v___y_3686_ = v_code_3592_;
goto v___jp_3685_;
}
}
}
v___jp_3685_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3687_ = lean_array_mk(v___x_3684_);
v___x_3688_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3682_, v___x_3687_, v___y_3686_);
lean_dec_ref(v___x_3687_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3688_);
v___x_3690_ = v___x_3680_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
v___jp_3692_:
{
lean_object* v___x_3694_; 
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 3, v_a_3678_);
v___x_3694_ = v___x_3673_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_typeName_3668_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_resultType_3669_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_discr_3670_);
lean_ctor_set(v_reuseFailAlloc_3696_, 3, v_a_3678_);
v___x_3694_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
v___y_3686_ = v___x_3695_;
goto v___jp_3685_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_newArms_3675_);
lean_del_object(v___x_3673_);
lean_dec_ref(v_alts_3671_);
lean_dec(v_discr_3670_);
lean_dec_ref(v_resultType_3669_);
lean_dec(v_typeName_3668_);
lean_dec_ref_known(v_code_3592_, 1);
v_a_3704_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3677_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3677_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v___x_3665_);
lean_dec_ref_known(v_code_3592_, 1);
lean_dec_ref(v_cases_3660_);
v_a_3713_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3666_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3666_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref_known(v_code_3592_, 1);
lean_dec_ref(v_cases_3660_);
v_a_3721_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3661_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3661_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
default: 
{
uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3729_ = 0;
lean_inc(v_a_3593_);
v___x_3730_ = lean_array_mk(v_a_3593_);
v___x_3731_ = l_Array_reverse___redArg(v___x_3730_);
v___x_3732_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3729_, v___x_3731_, v_code_3592_);
lean_dec_ref(v___x_3731_);
v___x_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
return v___x_3733_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3742_, lean_object* v_i_3743_, lean_object* v_as_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; uint8_t v___x_3752_; 
v___x_3751_ = lean_array_get_size(v_as_3744_);
v___x_3752_ = lean_nat_dec_lt(v_i_3743_, v___x_3751_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; 
lean_dec(v_i_3743_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_as_3744_);
return v___x_3753_;
}
else
{
lean_object* v_toCold_3754_; lean_object* v_options_3755_; lean_object* v_inheritedTraceOptions_3756_; uint8_t v_hasTrace_3757_; uint8_t v___x_3758_; lean_object* v_a_3759_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; 
v_toCold_3754_ = lean_ctor_get(v___y_3748_, 0);
v_options_3755_ = lean_ctor_get(v_toCold_3754_, 2);
v_inheritedTraceOptions_3756_ = lean_ctor_get(v_toCold_3754_, 11);
v_hasTrace_3757_ = lean_ctor_get_uint8(v_options_3755_, sizeof(void*)*1);
v___x_3758_ = 0;
v_a_3759_ = lean_array_fget_borrowed(v_as_3744_, v_i_3743_);
v___x_3790_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3759_);
v___x_3791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3742_, v___x_3790_);
if (v_hasTrace_3757_ == 0)
{
lean_dec(v___x_3790_);
v___y_3793_ = v___y_3746_;
v___y_3794_ = v___y_3747_;
v___y_3795_ = v___y_3748_;
v___y_3796_ = v___y_3749_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v___x_3801_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3802_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3756_, v_options_3755_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_dec(v___x_3790_);
v___y_3793_ = v___y_3746_;
v___y_3794_ = v___y_3747_;
v___y_3795_ = v___y_3748_;
v___y_3796_ = v___y_3749_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3804_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3790_, v___x_3805_);
v___x_3807_ = l_Lean_MessageData_ofFormat(v___x_3806_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3804_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_List_lengthTR___redArg(v___x_3791_);
v___x_3812_ = l_Nat_reprFast(v___x_3811_);
v___x_3813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
v___x_3814_ = l_Lean_MessageData_ofFormat(v___x_3813_);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3810_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3801_, v___x_3815_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_dec_ref_known(v___x_3816_, 1);
v___y_3793_ = v___y_3746_;
v___y_3794_ = v___y_3747_;
v___y_3795_ = v___y_3748_;
v___y_3796_ = v___y_3749_;
goto v___jp_3792_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v___x_3791_);
lean_dec_ref(v_as_3744_);
lean_dec(v_i_3743_);
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
v___jp_3760_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3758_, v___y_3764_, v___y_3766_);
lean_dec_ref(v___y_3764_);
v___x_3768_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3768_, 0, v___x_3767_);
v___x_3769_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3768_, v___y_3763_, v___y_3765_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; size_t v___x_3772_; size_t v___x_3773_; uint8_t v___x_3774_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
lean_inc(v_a_3759_);
v___x_3771_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3759_, v_a_3770_);
v___x_3772_ = lean_ptr_addr(v_a_3759_);
v___x_3773_ = lean_ptr_addr(v___x_3771_);
v___x_3774_ = lean_usize_dec_eq(v___x_3772_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_add(v_i_3743_, v___x_3775_);
v___x_3777_ = lean_array_fset(v_as_3744_, v_i_3743_, v___x_3771_);
lean_dec(v_i_3743_);
v_i_3743_ = v___x_3776_;
v_as_3744_ = v___x_3777_;
goto _start;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
lean_dec_ref(v___x_3771_);
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_nat_add(v_i_3743_, v___x_3779_);
lean_dec(v_i_3743_);
v_i_3743_ = v___x_3780_;
goto _start;
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec_ref(v_as_3744_);
lean_dec(v_i_3743_);
v_a_3782_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3769_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3769_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
v___jp_3792_:
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_array_mk(v___x_3791_);
switch(lean_obj_tag(v_a_3759_))
{
case 0:
{
lean_object* v_code_3798_; 
v_code_3798_ = lean_ctor_get(v_a_3759_, 2);
lean_inc_ref(v_code_3798_);
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3796_;
v___y_3763_ = v___y_3793_;
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___y_3794_;
v___y_3766_ = v_code_3798_;
goto v___jp_3760_;
}
case 1:
{
lean_object* v_code_3799_; 
v_code_3799_ = lean_ctor_get(v_a_3759_, 1);
lean_inc_ref(v_code_3799_);
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3796_;
v___y_3763_ = v___y_3793_;
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___y_3794_;
v___y_3766_ = v_code_3799_;
goto v___jp_3760_;
}
default: 
{
lean_object* v_code_3800_; 
v_code_3800_ = lean_ctor_get(v_a_3759_, 0);
lean_inc_ref(v_code_3800_);
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3796_;
v___y_3763_ = v___y_3793_;
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___y_3794_;
v___y_3766_ = v_code_3800_;
goto v___jp_3760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3825_, lean_object* v_i_3826_, lean_object* v_as_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3825_, v_i_3826_, v_as_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___x_3825_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3835_, lean_object* v_v_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
if (lean_obj_tag(v_v_3836_) == 0)
{
lean_object* v_code_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3867_; 
v_code_3843_ = lean_ctor_get(v_v_3836_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_v_3836_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3845_ = v_v_3836_;
v_isShared_3846_ = v_isSharedCheck_3867_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_code_3843_);
lean_dec(v_v_3836_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3867_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; 
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
v___x_3847_ = lean_apply_7(v_f_3835_, v_code_3843_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, lean_box(0));
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3858_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3850_ = v___x_3847_;
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v_a_3848_);
v___x_3853_ = v___x_3845_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v___x_3853_);
v___x_3855_ = v___x_3850_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_del_object(v___x_3845_);
v_a_3859_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3847_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3847_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
else
{
lean_object* v___x_3868_; 
lean_dec_ref(v_f_3835_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v_v_3836_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3869_, lean_object* v_v_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3869_, v_v_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3878_, lean_object* v_f_3879_, lean_object* v_v_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3879_, v_v_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3888_, lean_object* v_f_3889_, lean_object* v_v_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
uint8_t v_pu_boxed_3897_; lean_object* v_res_3898_; 
v_pu_boxed_3897_ = lean_unbox(v_pu_3888_);
v_res_3898_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_3897_, v_f_3889_, v_v_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_toSignature_3906_; lean_object* v_value_3907_; uint8_t v_recursive_3908_; lean_object* v_inlineAttr_x3f_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3935_; 
v_toSignature_3906_ = lean_ctor_get(v_decl_3900_, 0);
v_value_3907_ = lean_ctor_get(v_decl_3900_, 1);
v_recursive_3908_ = lean_ctor_get_uint8(v_decl_3900_, sizeof(void*)*3);
v_inlineAttr_x3f_3909_ = lean_ctor_get(v_decl_3900_, 2);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_decl_3900_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3911_ = v_decl_3900_;
v_isShared_3912_ = v_isSharedCheck_3935_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_inlineAttr_x3f_3909_);
lean_inc(v_value_3907_);
lean_inc(v_toSignature_3906_);
lean_dec(v_decl_3900_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3935_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3913_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_3914_ = lean_box(0);
v___x_3915_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_3913_, v_value_3907_, v___x_3914_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3926_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 1, v_a_3916_);
v___x_3921_ = v___x_3911_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_toSignature_3906_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_a_3916_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_inlineAttr_x3f_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3925_, sizeof(void*)*3, v_recursive_3908_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3921_);
v___x_3923_ = v___x_3918_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_del_object(v___x_3911_);
lean_dec(v_inlineAttr_x3f_3909_);
lean_dec_ref(v_toSignature_3906_);
v_a_3927_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3915_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3915_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_3959_, lean_object* v___f_3960_, lean_object* v_occurrence_3961_, lean_object* v_h_3962_){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_3964_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3963_, v_phase_3959_, v___f_3960_, v_occurrence_3961_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_3965_, lean_object* v___f_3966_, lean_object* v_occurrence_3967_, lean_object* v_h_3968_){
_start:
{
uint8_t v_phase_boxed_3969_; lean_object* v_res_3970_; 
v_phase_boxed_3969_ = lean_unbox(v_phase_3965_);
v_res_3970_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_3969_, v___f_3966_, v_occurrence_3967_, v_h_3968_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_3972_, lean_object* v_occurrence_3973_){
_start:
{
lean_object* v___f_3974_; lean_object* v___x_3975_; lean_object* v___f_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; 
v___f_3974_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_3975_ = lean_box(v_phase_3972_);
v___f_3976_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3976_, 0, v___x_3975_);
lean_closure_set(v___f_3976_, 1, v___f_3974_);
lean_closure_set(v___f_3976_, 2, v_occurrence_3973_);
v___x_3977_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_3978_ = 0;
v___x_3979_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_3977_, v_phase_3972_, v___x_3978_, v___f_3976_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_3980_, lean_object* v_occurrence_3981_){
_start:
{
uint8_t v_phase_boxed_3982_; lean_object* v_res_3983_; 
v_phase_boxed_3982_ = lean_unbox(v_phase_3980_);
v_res_3983_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_3982_, v_occurrence_3981_);
return v_res_3983_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = lean_unsigned_to_nat(3411573818u);
v___x_4036_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4037_ = l_Lean_Name_num___override(v___x_4036_, v___x_4035_);
return v___x_4037_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4040_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4041_ = l_Lean_Name_str___override(v___x_4040_, v___x_4039_);
return v___x_4041_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4044_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4045_ = l_Lean_Name_str___override(v___x_4044_, v___x_4043_);
return v___x_4045_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = lean_unsigned_to_nat(2u);
v___x_4047_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4048_ = l_Lean_Name_num___override(v___x_4047_, v___x_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4050_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4051_ = 1;
v___x_4052_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4053_ = l_Lean_registerTraceClass(v___x_4050_, v___x_4051_, v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4055_;
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
