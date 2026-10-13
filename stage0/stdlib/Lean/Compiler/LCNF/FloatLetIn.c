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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_name_7_; lean_object* v___x_8_; 
v_name_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_name_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_name_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim___redArg(lean_object* v_t_21_, lean_object* v_arm_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_21_, v_arm_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_arm_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_25_, v_arm_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim___redArg(lean_object* v_t_29_, lean_object* v_default_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_29_, v_default_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_default_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_33_, v_default_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim___redArg(lean_object* v_t_37_, lean_object* v_dont_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_37_, v_dont_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_dont_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_41_, v_dont_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim___redArg(lean_object* v_t_45_, lean_object* v_unknown_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_45_, v_unknown_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_unknown_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_49_, v_unknown_51_);
return v___x_52_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(lean_object* v_x_53_){
_start:
{
switch(lean_obj_tag(v_x_53_))
{
case 0:
{
lean_object* v_name_54_; uint64_t v___x_55_; 
v_name_54_ = lean_ctor_get(v_x_53_, 0);
v___x_55_ = 0ULL;
if (lean_obj_tag(v_name_54_) == 0)
{
uint64_t v___x_56_; 
v___x_56_ = 8934034000889494153ULL;
return v___x_56_;
}
else
{
uint64_t v_hash_57_; uint64_t v___x_58_; 
v_hash_57_ = lean_ctor_get_uint64(v_name_54_, sizeof(void*)*2);
v___x_58_ = lean_uint64_mix_hash(v___x_55_, v_hash_57_);
return v___x_58_;
}
}
case 1:
{
uint64_t v___x_59_; 
v___x_59_ = 1ULL;
return v___x_59_;
}
case 2:
{
uint64_t v___x_60_; 
v___x_60_ = 2ULL;
return v___x_60_;
}
default: 
{
uint64_t v___x_61_; 
v___x_61_ = 3ULL;
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed(lean_object* v_x_62_){
_start:
{
uint64_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_x_62_);
lean_dec(v_x_62_);
v_r_64_ = lean_box_uint64(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
switch(lean_obj_tag(v_x_67_))
{
case 0:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v_name_69_; lean_object* v_name_70_; uint8_t v___x_71_; 
v_name_69_ = lean_ctor_get(v_x_67_, 0);
v_name_70_ = lean_ctor_get(v_x_68_, 0);
v___x_71_ = lean_name_eq(v_name_69_, v_name_70_);
return v___x_71_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
}
case 1:
{
if (lean_obj_tag(v_x_68_) == 1)
{
uint8_t v___x_73_; 
v___x_73_ = 1;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
case 2:
{
if (lean_obj_tag(v_x_68_) == 2)
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
default: 
{
if (lean_obj_tag(v_x_68_) == 3)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_x_79_, v_x_80_);
lean_dec(v_x_80_);
lean_dec(v_x_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_nat_to_int(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_to_int(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(lean_object* v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v___y_111_; lean_object* v___y_118_; lean_object* v___y_125_; 
switch(lean_obj_tag(v_x_108_))
{
case 0:
{
lean_object* v_name_131_; lean_object* v___y_133_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_name_131_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_name_131_);
lean_dec_ref_known(v_x_108_, 1);
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_109_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_133_ = v___x_144_;
goto v___jp_132_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_133_ = v___x_145_;
goto v___jp_132_;
}
v___jp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_134_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8));
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = l_Lean_Name_reprPrec(v_name_131_, v___x_135_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_134_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
lean_inc(v___y_133_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_133_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_109_);
return v___x_141_;
}
}
case 1:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1024u);
v___x_147_ = lean_nat_dec_le(v___x_146_, v_prec_109_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_111_ = v___x_148_;
goto v___jp_110_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_111_ = v___x_149_;
goto v___jp_110_;
}
}
case 2:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1024u);
v___x_151_ = lean_nat_dec_le(v___x_150_, v_prec_109_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_118_ = v___x_152_;
goto v___jp_117_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_118_ = v___x_153_;
goto v___jp_117_;
}
}
default: 
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1024u);
v___x_155_ = lean_nat_dec_le(v___x_154_, v_prec_109_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_125_ = v___x_156_;
goto v___jp_124_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_125_ = v___x_157_;
goto v___jp_124_;
}
}
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1));
lean_inc(v___y_111_);
v___x_113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_113_, 0, v___y_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = 0;
v___x_115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
v___x_116_ = l_Repr_addAppParen(v___x_115_, v_prec_109_);
return v___x_116_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3));
lean_inc(v___y_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___y_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_121_);
v___x_123_ = l_Repr_addAppParen(v___x_122_, v_prec_109_);
return v___x_123_;
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5));
lean_inc(v___y_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = l_Repr_addAppParen(v___x_129_, v_prec_109_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed(lean_object* v_x_158_, lean_object* v_prec_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v_x_158_, v_prec_159_);
lean_dec(v_prec_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_ctorName_164_; lean_object* v___x_165_; 
v_ctorName_164_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_ctorName_164_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v_ctorName_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(1);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_x_167_);
lean_dec_ref(v_x_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object* v_decl_169_, lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_inc(v_a_171_);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v_decl_169_);
lean_ctor_set(v___x_177_, 1, v_a_171_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
v___x_178_ = lean_apply_6(v_x_170_, v___x_177_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, lean_box(0));
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg___boxed(lean_object* v_decl_179_, lean_object* v_x_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_179_, v_x_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* v_00_u03b1_188_, lean_object* v_decl_189_, lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_189_, v_x_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___boxed(lean_object* v_00_u03b1_198_, lean_object* v_decl_199_, lean_object* v_x_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(v_00_u03b1_198_, v_decl_199_, v_x_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_box(0);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
v___x_215_ = lean_apply_6(v_x_208_, v___x_214_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, lean_box(0));
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg___boxed(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* v_00_u03b1_223_, lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_224_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object* v_00_u03b1_232_, lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(v_00_u03b1_232_, v_x_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object* v_decl_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_type_247_; lean_object* v_value_248_; lean_object* v___x_249_; 
v_type_247_ = lean_ctor_get(v_decl_241_, 2);
lean_inc_ref(v_type_247_);
v_value_248_ = lean_ctor_get(v_decl_241_, 3);
lean_inc(v_value_248_);
lean_dec_ref(v_decl_241_);
v___x_249_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_247_, v_a_245_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_298_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_298_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_298_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_298_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
if (lean_obj_tag(v_a_250_) == 0)
{
uint8_t v___x_254_; 
v___x_254_ = 0;
if (lean_obj_tag(v_value_248_) == 2)
{
lean_object* v_struct_255_; lean_object* v___x_256_; 
lean_del_object(v___x_252_);
v_struct_255_ = lean_ctor_get(v_value_248_, 2);
lean_inc(v_struct_255_);
lean_dec_ref_known(v_value_248_, 3);
v___x_256_ = l_Lean_Compiler_LCNF_getType(v_struct_255_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_a_257_, v_a_245_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_272_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_272_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_272_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
if (lean_obj_tag(v_a_259_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_box(v___x_254_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
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
uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
lean_dec_ref_known(v_a_259_, 1);
v___x_267_ = 1;
v___x_268_ = lean_box(v___x_267_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_268_);
v___x_270_ = v___x_261_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_258_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_258_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
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
v_a_281_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_256_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_256_);
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
lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec(v_value_248_);
v___x_289_ = lean_box(v___x_254_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_289_);
v___x_291_ = v___x_252_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec_ref_known(v_a_250_, 1);
lean_dec(v_value_248_);
v___x_293_ = 1;
v___x_294_ = lean_box(v___x_293_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_294_);
v___x_296_ = v___x_252_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_value_248_);
v_a_299_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_249_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_249_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object* v_decl_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* v_decl_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_314_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object* v_decl_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(v_decl_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object* v_a_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
else
{
lean_object* v_key_333_; lean_object* v_tail_334_; uint8_t v___x_335_; 
v_key_333_ = lean_ctor_get(v_x_331_, 0);
v_tail_334_ = lean_ctor_get(v_x_331_, 2);
v___x_335_ = l_Lean_instBEqFVarId_beq(v_key_333_, v_a_330_);
if (v___x_335_ == 0)
{
v_x_331_ = v_tail_334_;
goto _start;
}
else
{
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec(v_a_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_buckets_343_; lean_object* v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v_fold_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_buckets_343_ = lean_ctor_get(v_m_341_, 1);
v___x_344_ = lean_array_get_size(v_buckets_343_);
v___x_345_ = l_Lean_instHashableFVarId_hash(v_a_342_);
v___x_346_ = 32ULL;
v___x_347_ = lean_uint64_shift_right(v___x_345_, v___x_346_);
v_fold_348_ = lean_uint64_xor(v___x_345_, v___x_347_);
v___x_349_ = 16ULL;
v___x_350_ = lean_uint64_shift_right(v_fold_348_, v___x_349_);
v___x_351_ = lean_uint64_xor(v_fold_348_, v___x_350_);
v___x_352_ = lean_uint64_to_usize(v___x_351_);
v___x_353_ = lean_usize_of_nat(v___x_344_);
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_sub(v___x_353_, v___x_354_);
v___x_356_ = lean_usize_land(v___x_352_, v___x_355_);
v___x_357_ = lean_array_uget_borrowed(v_buckets_343_, v___x_356_);
v___x_358_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_342_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_m_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
return v_x_363_;
}
else
{
lean_object* v_key_365_; lean_object* v_value_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_390_; 
v_key_365_ = lean_ctor_get(v_x_364_, 0);
v_value_366_ = lean_ctor_get(v_x_364_, 1);
v_tail_367_ = lean_ctor_get(v_x_364_, 2);
v_isSharedCheck_390_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_390_ == 0)
{
v___x_369_ = v_x_364_;
v_isShared_370_ = v_isSharedCheck_390_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_value_366_);
lean_inc(v_key_365_);
lean_dec(v_x_364_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_390_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v_fold_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_371_ = lean_array_get_size(v_x_363_);
v___x_372_ = l_Lean_instHashableFVarId_hash(v_key_365_);
v___x_373_ = 32ULL;
v___x_374_ = lean_uint64_shift_right(v___x_372_, v___x_373_);
v_fold_375_ = lean_uint64_xor(v___x_372_, v___x_374_);
v___x_376_ = 16ULL;
v___x_377_ = lean_uint64_shift_right(v_fold_375_, v___x_376_);
v___x_378_ = lean_uint64_xor(v_fold_375_, v___x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = lean_usize_of_nat(v___x_371_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_sub(v___x_380_, v___x_381_);
v___x_383_ = lean_usize_land(v___x_379_, v___x_382_);
v___x_384_ = lean_array_uget_borrowed(v_x_363_, v___x_383_);
lean_inc(v___x_384_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 2, v___x_384_);
v___x_386_ = v___x_369_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_key_365_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_value_366_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_384_);
v___x_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
v___x_387_ = lean_array_uset(v_x_363_, v___x_383_, v___x_386_);
v_x_363_ = v___x_387_;
v_x_364_ = v_tail_367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(lean_object* v_i_391_, lean_object* v_source_392_, lean_object* v_target_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_source_392_);
v___x_395_ = lean_nat_dec_lt(v_i_391_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec_ref(v_source_392_);
lean_dec(v_i_391_);
return v_target_393_;
}
else
{
lean_object* v_es_396_; lean_object* v___x_397_; lean_object* v_source_398_; lean_object* v_target_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_es_396_ = lean_array_fget(v_source_392_, v_i_391_);
v___x_397_ = lean_box(0);
v_source_398_ = lean_array_fset(v_source_392_, v_i_391_, v___x_397_);
v_target_399_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_target_393_, v_es_396_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_i_391_, v___x_400_);
lean_dec(v_i_391_);
v_i_391_ = v___x_401_;
v_source_392_ = v_source_398_;
v_target_393_ = v_target_399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object* v_data_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_nbuckets_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_404_ = lean_array_get_size(v_data_403_);
v___x_405_ = lean_unsigned_to_nat(2u);
v_nbuckets_406_ = lean_nat_mul(v___x_404_, v___x_405_);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_box(0);
v___x_409_ = lean_mk_array(v_nbuckets_406_, v___x_408_);
v___x_410_ = lean_array_propagate_mark(v_data_403_, v___x_409_);
v___x_411_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v___x_407_, v_data_403_, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object* v_m_412_, lean_object* v_a_413_, lean_object* v_b_414_){
_start:
{
lean_object* v_size_415_; lean_object* v_buckets_416_; lean_object* v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v_fold_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v_bkt_430_; uint8_t v___x_431_; 
v_size_415_ = lean_ctor_get(v_m_412_, 0);
v_buckets_416_ = lean_ctor_get(v_m_412_, 1);
v___x_417_ = lean_array_get_size(v_buckets_416_);
v___x_418_ = l_Lean_instHashableFVarId_hash(v_a_413_);
v___x_419_ = 32ULL;
v___x_420_ = lean_uint64_shift_right(v___x_418_, v___x_419_);
v_fold_421_ = lean_uint64_xor(v___x_418_, v___x_420_);
v___x_422_ = 16ULL;
v___x_423_ = lean_uint64_shift_right(v_fold_421_, v___x_422_);
v___x_424_ = lean_uint64_xor(v_fold_421_, v___x_423_);
v___x_425_ = lean_uint64_to_usize(v___x_424_);
v___x_426_ = lean_usize_of_nat(v___x_417_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_sub(v___x_426_, v___x_427_);
v___x_429_ = lean_usize_land(v___x_425_, v___x_428_);
v_bkt_430_ = lean_array_uget_borrowed(v_buckets_416_, v___x_429_);
v___x_431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_413_, v_bkt_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_452_; 
lean_inc_ref(v_buckets_416_);
lean_inc(v_size_415_);
v_isSharedCheck_452_ = !lean_is_exclusive(v_m_412_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v_m_412_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_m_412_, 0);
lean_dec(v_unused_454_);
v___x_433_ = v_m_412_;
v_isShared_434_ = v_isSharedCheck_452_;
goto v_resetjp_432_;
}
else
{
lean_dec(v_m_412_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_452_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v_size_x27_436_; lean_object* v___x_437_; lean_object* v_buckets_x27_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v_size_x27_436_ = lean_nat_add(v_size_415_, v___x_435_);
lean_dec(v_size_415_);
lean_inc(v_bkt_430_);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v_a_413_);
lean_ctor_set(v___x_437_, 1, v_b_414_);
lean_ctor_set(v___x_437_, 2, v_bkt_430_);
v_buckets_x27_438_ = lean_array_uset(v_buckets_416_, v___x_429_, v___x_437_);
v___x_439_ = lean_unsigned_to_nat(4u);
v___x_440_ = lean_nat_mul(v_size_x27_436_, v___x_439_);
v___x_441_ = lean_unsigned_to_nat(3u);
v___x_442_ = lean_nat_div(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_array_get_size(v_buckets_x27_438_);
v___x_444_ = lean_nat_dec_le(v___x_442_, v___x_443_);
lean_dec(v___x_442_);
if (v___x_444_ == 0)
{
lean_object* v_val_445_; lean_object* v___x_447_; 
v_val_445_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_438_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_val_445_);
lean_ctor_set(v___x_433_, 0, v_size_x27_436_);
v___x_447_ = v___x_433_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_size_x27_436_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_val_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
else
{
lean_object* v___x_450_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_buckets_x27_438_);
lean_ctor_set(v___x_433_, 0, v_size_x27_436_);
v___x_450_ = v___x_433_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_size_x27_436_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_buckets_x27_438_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_dec(v_b_414_);
lean_dec(v_a_413_);
return v_m_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object* v_var_455_, uint8_t v_borrowed_456_, lean_object* v_a_457_){
_start:
{
if (lean_obj_tag(v_var_455_) == 1)
{
lean_object* v_fvarId_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_477_; 
v_fvarId_459_ = lean_ctor_get(v_var_455_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_var_455_);
if (v_isSharedCheck_477_ == 0)
{
v___x_461_ = v_var_455_;
v_isShared_462_ = v_isSharedCheck_477_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_fvarId_459_);
lean_dec(v_var_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_477_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_st_ref_get(v_a_457_);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_463_, v_fvarId_459_);
lean_dec(v___x_463_);
if (v_borrowed_456_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_465_ = lean_st_ref_take(v_a_457_);
v___x_466_ = lean_box(0);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_465_, v_fvarId_459_, v___x_466_);
v___x_468_ = lean_st_ref_put(v_a_457_, v___x_467_);
v___x_469_ = lean_box(v___x_464_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 0);
lean_ctor_set(v___x_461_, 0, v___x_469_);
v___x_471_ = v___x_461_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_475_; 
lean_dec(v_fvarId_459_);
v___x_473_ = lean_box(v___x_464_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 0);
lean_ctor_set(v___x_461_, 0, v___x_473_);
v___x_475_ = v___x_461_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_var_455_);
v___x_478_ = 0;
v___x_479_ = lean_box(v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object* v_var_481_, lean_object* v_borrowed_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
uint8_t v_borrowed_boxed_485_; lean_object* v_res_486_; 
v_borrowed_boxed_485_ = lean_unbox(v_borrowed_482_);
v_res_486_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_481_, v_borrowed_boxed_485_, v_a_483_);
lean_dec(v_a_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object* v_var_487_, uint8_t v_borrowed_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_487_, v_borrowed_488_, v_a_489_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object* v_var_496_, lean_object* v_borrowed_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
uint8_t v_borrowed_boxed_504_; lean_object* v_res_505_; 
v_borrowed_boxed_504_ = lean_unbox(v_borrowed_497_);
v_res_505_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_496_, v_borrowed_boxed_504_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
return v_res_505_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_a_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_507_, v_a_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object* v_00_u03b2_510_, lean_object* v_m_511_, lean_object* v_a_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_510_, v_m_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_m_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object* v_00_u03b2_515_, lean_object* v_m_516_, lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_516_, v_a_517_, v_b_518_);
return v___x_519_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_524_, v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec(v_a_525_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object* v_00_u03b2_529_, lean_object* v_data_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_data_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_532_, lean_object* v_i_533_, lean_object* v_source_534_, lean_object* v_target_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v_i_533_, v_source_534_, v_target_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_x_538_, v_x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object* v_as_541_, size_t v_i_542_, size_t v_stop_543_, uint8_t v_b_544_, lean_object* v___y_545_){
_start:
{
uint8_t v_a_548_; lean_object* v___y_553_; uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_eq(v_i_542_, v_stop_543_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_array_uget_borrowed(v_as_541_, v_i_542_);
lean_inc(v___x_557_);
v___x_558_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_557_, v___x_556_, v___y_545_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v___x_560_ = lean_unbox(v_a_559_);
if (v___x_560_ == 0)
{
lean_dec_ref_known(v___x_558_, 1);
v_a_548_ = v_b_544_;
goto v___jp_547_;
}
else
{
v___y_553_ = v___x_558_;
goto v___jp_552_;
}
}
else
{
v___y_553_ = v___x_558_;
goto v___jp_552_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_box(v_b_544_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
v___jp_547_:
{
size_t v___x_549_; size_t v___x_550_; 
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_542_, v___x_549_);
v_i_542_ = v___x_550_;
v_b_544_ = v_a_548_;
goto _start;
}
v___jp_552_:
{
if (lean_obj_tag(v___y_553_) == 0)
{
lean_object* v_a_554_; uint8_t v___x_555_; 
v_a_554_ = lean_ctor_get(v___y_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___y_553_, 1);
v___x_555_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
v_a_548_ = v___x_555_;
goto v___jp_547_;
}
else
{
return v___y_553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_563_, lean_object* v_i_564_, lean_object* v_stop_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
size_t v_i_boxed_569_; size_t v_stop_boxed_570_; uint8_t v_b_boxed_571_; lean_object* v_res_572_; 
v_i_boxed_569_ = lean_unbox_usize(v_i_564_);
lean_dec(v_i_564_);
v_stop_boxed_570_ = lean_unbox_usize(v_stop_565_);
lean_dec(v_stop_565_);
v_b_boxed_571_ = lean_unbox(v_b_566_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_563_, v_i_boxed_569_, v_stop_boxed_570_, v_b_boxed_571_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v_as_563_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_573_, lean_object* v_args_574_, lean_object* v_val_575_, lean_object* v_a_576_, uint8_t v_b_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_a_581_; uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_lt(v_a_576_, v_upperBound_573_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_a_576_);
v___x_586_ = lean_box(v_b_577_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
else
{
lean_object* v_params_588_; lean_object* v___x_589_; uint8_t v___y_591_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_params_588_ = lean_ctor_get(v_val_575_, 3);
v___x_589_ = lean_array_fget_borrowed(v_args_574_, v_a_576_);
v___x_595_ = lean_array_get_size(v_params_588_);
v___x_596_ = lean_nat_dec_lt(v_a_576_, v___x_595_);
if (v___x_596_ == 0)
{
v___y_591_ = v___x_596_;
goto v___jp_590_;
}
else
{
lean_object* v___x_597_; uint8_t v_borrow_598_; 
v___x_597_ = lean_array_fget_borrowed(v_params_588_, v_a_576_);
v_borrow_598_ = lean_ctor_get_uint8(v___x_597_, sizeof(void*)*3);
v___y_591_ = v_borrow_598_;
goto v___jp_590_;
}
v___jp_590_:
{
lean_object* v___x_592_; 
lean_inc(v___x_589_);
v___x_592_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_589_, v___y_591_, v___y_578_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; uint8_t v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
if (v___x_594_ == 0)
{
v_a_581_ = v_b_577_;
goto v___jp_580_;
}
else
{
v_a_581_ = v___x_585_;
goto v___jp_580_;
}
}
else
{
lean_dec(v_a_576_);
return v___x_592_;
}
}
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_a_576_, v___x_582_);
lean_dec(v_a_576_);
v_a_576_ = v___x_583_;
v_b_577_ = v_a_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object* v_upperBound_599_, lean_object* v_args_600_, lean_object* v_val_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
uint8_t v_b_boxed_606_; lean_object* v_res_607_; 
v_b_boxed_606_ = lean_unbox(v_b_603_);
v_res_607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_599_, v_args_600_, v_val_601_, v_a_602_, v_b_boxed_606_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v_val_601_);
lean_dec_ref(v_args_600_);
lean_dec(v_upperBound_599_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object* v_as_608_, size_t v_i_609_, size_t v_stop_610_, uint8_t v_b_611_, lean_object* v___y_612_){
_start:
{
uint8_t v_a_615_; lean_object* v___y_620_; uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_609_, v_stop_610_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_array_uget_borrowed(v_as_608_, v_i_609_);
lean_inc(v___x_624_);
v___x_625_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_624_, v___x_623_, v___y_612_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; uint8_t v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v___x_627_ = lean_unbox(v_a_626_);
if (v___x_627_ == 0)
{
lean_dec_ref_known(v___x_625_, 1);
v_a_615_ = v_b_611_;
goto v___jp_614_;
}
else
{
v___y_620_ = v___x_625_;
goto v___jp_619_;
}
}
else
{
v___y_620_ = v___x_625_;
goto v___jp_619_;
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(v_b_611_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
v___jp_614_:
{
size_t v___x_616_; size_t v___x_617_; 
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_609_, v___x_616_);
v_i_609_ = v___x_617_;
v_b_611_ = v_a_615_;
goto _start;
}
v___jp_619_:
{
if (lean_obj_tag(v___y_620_) == 0)
{
lean_object* v_a_621_; uint8_t v___x_622_; 
v_a_621_ = lean_ctor_get(v___y_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___y_620_, 1);
v___x_622_ = lean_unbox(v_a_621_);
lean_dec(v_a_621_);
v_a_615_ = v___x_622_;
goto v___jp_614_;
}
else
{
return v___y_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_stop_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; uint8_t v_b_boxed_638_; lean_object* v_res_639_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_632_);
lean_dec(v_stop_632_);
v_b_boxed_638_ = lean_unbox(v_b_633_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_630_, v_i_boxed_636_, v_stop_boxed_637_, v_b_boxed_638_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v_as_630_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object* v_value_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
switch(lean_obj_tag(v_value_640_))
{
case 2:
{
lean_object* v_struct_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; 
v_struct_647_ = lean_ctor_get(v_value_640_, 2);
lean_inc(v_struct_647_);
lean_dec_ref_known(v_value_640_, 3);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_struct_647_);
v___x_649_ = 1;
v___x_650_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_648_, v___x_649_, v_a_641_);
return v___x_650_;
}
case 3:
{
lean_object* v_declName_651_; lean_object* v_args_652_; lean_object* v___x_653_; 
v_declName_651_ = lean_ctor_get(v_value_640_, 0);
lean_inc(v_declName_651_);
v_args_652_ = lean_ctor_get(v_value_640_, 2);
lean_inc_ref(v_args_652_);
lean_dec_ref_known(v_value_640_, 3);
v___x_653_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_651_, v_a_645_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_682_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_682_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_682_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_682_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
if (lean_obj_tag(v_a_654_) == 0)
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_658_ = 0;
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_array_get_size(v_args_652_);
v___x_661_ = lean_nat_dec_lt(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec_ref(v_args_652_);
v___x_662_ = lean_box(v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_662_);
v___x_664_ = v___x_656_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_le(v___x_660_, v___x_660_);
if (v___x_666_ == 0)
{
if (v___x_661_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec_ref(v_args_652_);
v___x_667_ = lean_box(v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_667_);
v___x_669_ = v___x_656_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_656_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_660_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_652_, v___x_671_, v___x_672_, v___x_658_, v_a_641_);
lean_dec_ref(v_args_652_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
lean_del_object(v___x_656_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_660_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_652_, v___x_674_, v___x_675_, v___x_658_, v_a_641_);
lean_dec_ref(v_args_652_);
return v___x_676_;
}
}
}
else
{
lean_object* v_val_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; 
lean_del_object(v___x_656_);
v_val_677_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_a_654_, 1);
v___x_678_ = lean_array_get_size(v_args_652_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = 0;
v___x_681_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_678_, v_args_652_, v_val_677_, v___x_679_, v___x_680_, v_a_641_);
lean_dec(v_val_677_);
lean_dec_ref(v_args_652_);
return v___x_681_;
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_args_652_);
v_a_683_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_653_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_653_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_691_; lean_object* v_args_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_fvarId_691_ = lean_ctor_get(v_value_640_, 0);
lean_inc(v_fvarId_691_);
v_args_692_ = lean_ctor_get(v_value_640_, 1);
lean_inc_ref(v_args_692_);
lean_dec_ref_known(v_value_640_, 2);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_fvarId_691_);
v___x_694_ = 0;
v___x_695_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_693_, v___x_694_, v_a_641_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_array_get_size(v_args_692_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec_ref(v_args_692_);
return v___x_695_;
}
else
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_le(v___x_698_, v___x_698_);
if (v___x_700_ == 0)
{
if (v___x_699_ == 0)
{
lean_dec_ref(v_args_692_);
return v___x_695_;
}
else
{
size_t v___x_701_; size_t v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; 
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_698_);
v___x_703_ = lean_unbox(v_a_696_);
lean_dec(v_a_696_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_692_, v___x_701_, v___x_702_, v___x_703_, v_a_641_);
lean_dec_ref(v_args_692_);
return v___x_704_;
}
}
else
{
size_t v___x_705_; size_t v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; 
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_698_);
v___x_707_ = lean_unbox(v_a_696_);
lean_dec(v_a_696_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_692_, v___x_705_, v___x_706_, v___x_707_, v_a_641_);
lean_dec_ref(v_args_692_);
return v___x_708_;
}
}
}
default: 
{
uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_value_640_);
v___x_709_ = 0;
v___x_710_ = lean_box(v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(lean_object* v_value_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object* v_env_720_, lean_object* v_value_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object* v_env_729_, lean_object* v_value_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_729_, v_value_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_env_729_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, uint8_t v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_738_, v_i_739_, v_stop_740_, v_b_741_, v___y_742_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_stop_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
size_t v_i_boxed_759_; size_t v_stop_boxed_760_; uint8_t v_b_boxed_761_; lean_object* v_res_762_; 
v_i_boxed_759_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_stop_boxed_760_ = lean_unbox_usize(v_stop_751_);
lean_dec(v_stop_751_);
v_b_boxed_761_ = lean_unbox(v_b_752_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_749_, v_i_boxed_759_, v_stop_boxed_760_, v_b_boxed_761_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v_as_749_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object* v_upperBound_763_, lean_object* v_args_764_, lean_object* v_val_765_, lean_object* v_inst_766_, lean_object* v_R_767_, lean_object* v_a_768_, uint8_t v_b_769_, lean_object* v_c_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_763_, v_args_764_, v_val_765_, v_a_768_, v_b_769_, v___y_771_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object* v_upperBound_778_, lean_object* v_args_779_, lean_object* v_val_780_, lean_object* v_inst_781_, lean_object* v_R_782_, lean_object* v_a_783_, lean_object* v_b_784_, lean_object* v_c_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_b_boxed_792_; lean_object* v_res_793_; 
v_b_boxed_792_ = lean_unbox(v_b_784_);
v_res_793_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_778_, v_args_779_, v_val_780_, v_inst_781_, v_R_782_, v_a_783_, v_b_boxed_792_, v_c_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v_val_780_);
lean_dec_ref(v_args_779_);
lean_dec(v_upperBound_778_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object* v_as_794_, size_t v_i_795_, size_t v_stop_796_, uint8_t v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_794_, v_i_795_, v_stop_796_, v_b_797_, v___y_798_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_stop_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
size_t v_i_boxed_815_; size_t v_stop_boxed_816_; uint8_t v_b_boxed_817_; lean_object* v_res_818_; 
v_i_boxed_815_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_stop_boxed_816_ = lean_unbox_usize(v_stop_807_);
lean_dec(v_stop_807_);
v_b_boxed_817_ = lean_unbox(v_b_808_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_805_, v_i_boxed_815_, v_stop_boxed_816_, v_b_boxed_817_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v_as_805_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object* v_value_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
if (lean_obj_tag(v_value_819_) == 0)
{
lean_object* v_decl_826_; lean_object* v_value_827_; lean_object* v___x_828_; 
v_decl_826_ = lean_ctor_get(v_value_819_, 0);
lean_inc_ref(v_decl_826_);
lean_dec_ref_known(v_value_819_, 1);
v_value_827_ = lean_ctor_get(v_decl_826_, 3);
lean_inc(v_value_827_);
lean_dec_ref(v_decl_826_);
v___x_828_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_827_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
return v___x_828_;
}
else
{
uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v_value_819_);
v___x_829_ = 0;
v___x_830_ = lean_box(v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object* v_value_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object* v_env_840_, lean_object* v_value_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object* v_env_849_, lean_object* v_value_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_849_, v_value_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_env_849_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(lean_object* v_a_858_, lean_object* v_b_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_dec(v_b_859_);
lean_dec(v_a_858_);
return v_x_860_;
}
else
{
lean_object* v_key_861_; lean_object* v_value_862_; lean_object* v_tail_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_875_; 
v_key_861_ = lean_ctor_get(v_x_860_, 0);
v_value_862_ = lean_ctor_get(v_x_860_, 1);
v_tail_863_ = lean_ctor_get(v_x_860_, 2);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_860_);
if (v_isSharedCheck_875_ == 0)
{
v___x_865_ = v_x_860_;
v_isShared_866_ = v_isSharedCheck_875_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_tail_863_);
lean_inc(v_value_862_);
lean_inc(v_key_861_);
lean_dec(v_x_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_875_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = l_Lean_instBEqFVarId_beq(v_key_861_, v_a_858_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_858_, v_b_859_, v_tail_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 2, v___x_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_key_861_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_value_862_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
lean_object* v___x_873_; 
lean_dec(v_value_862_);
lean_dec(v_key_861_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v_b_859_);
lean_ctor_set(v___x_865_, 0, v_a_858_);
v___x_873_ = v___x_865_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_858_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_b_859_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_tail_863_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(lean_object* v_m_876_, lean_object* v_a_877_, lean_object* v_b_878_){
_start:
{
lean_object* v_size_879_; lean_object* v_buckets_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_923_; 
v_size_879_ = lean_ctor_get(v_m_876_, 0);
v_buckets_880_ = lean_ctor_get(v_m_876_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_m_876_);
if (v_isSharedCheck_923_ == 0)
{
v___x_882_ = v_m_876_;
v_isShared_883_ = v_isSharedCheck_923_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_buckets_880_);
lean_inc(v_size_879_);
lean_dec(v_m_876_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_923_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v_fold_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v_bkt_897_; uint8_t v___x_898_; 
v___x_884_ = lean_array_get_size(v_buckets_880_);
v___x_885_ = l_Lean_instHashableFVarId_hash(v_a_877_);
v___x_886_ = 32ULL;
v___x_887_ = lean_uint64_shift_right(v___x_885_, v___x_886_);
v_fold_888_ = lean_uint64_xor(v___x_885_, v___x_887_);
v___x_889_ = 16ULL;
v___x_890_ = lean_uint64_shift_right(v_fold_888_, v___x_889_);
v___x_891_ = lean_uint64_xor(v_fold_888_, v___x_890_);
v___x_892_ = lean_uint64_to_usize(v___x_891_);
v___x_893_ = lean_usize_of_nat(v___x_884_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_sub(v___x_893_, v___x_894_);
v___x_896_ = lean_usize_land(v___x_892_, v___x_895_);
v_bkt_897_ = lean_array_uget_borrowed(v_buckets_880_, v___x_896_);
v___x_898_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_877_, v_bkt_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v_size_x27_900_; lean_object* v___x_901_; lean_object* v_buckets_x27_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v_size_x27_900_ = lean_nat_add(v_size_879_, v___x_899_);
lean_dec(v_size_879_);
lean_inc(v_bkt_897_);
v___x_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_901_, 0, v_a_877_);
lean_ctor_set(v___x_901_, 1, v_b_878_);
lean_ctor_set(v___x_901_, 2, v_bkt_897_);
v_buckets_x27_902_ = lean_array_uset(v_buckets_880_, v___x_896_, v___x_901_);
v___x_903_ = lean_unsigned_to_nat(4u);
v___x_904_ = lean_nat_mul(v_size_x27_900_, v___x_903_);
v___x_905_ = lean_unsigned_to_nat(3u);
v___x_906_ = lean_nat_div(v___x_904_, v___x_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_array_get_size(v_buckets_x27_902_);
v___x_908_ = lean_nat_dec_le(v___x_906_, v___x_907_);
lean_dec(v___x_906_);
if (v___x_908_ == 0)
{
lean_object* v_val_909_; lean_object* v___x_911_; 
v_val_909_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_902_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_val_909_);
lean_ctor_set(v___x_882_, 0, v_size_x27_900_);
v___x_911_ = v___x_882_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_size_x27_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_val_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_914_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_buckets_x27_902_);
lean_ctor_set(v___x_882_, 0, v_size_x27_900_);
v___x_914_ = v___x_882_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_size_x27_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_buckets_x27_902_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
lean_object* v___x_916_; lean_object* v_buckets_x27_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_bkt_897_);
v___x_916_ = lean_box(0);
v_buckets_x27_917_ = lean_array_uset(v_buckets_880_, v___x_896_, v___x_916_);
v___x_918_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_877_, v_b_878_, v_bkt_897_);
v___x_919_ = lean_array_uset(v_buckets_x27_917_, v___x_896_, v___x_918_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_919_);
v___x_921_ = v___x_882_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_size_879_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_919_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(lean_object* v_a_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
lean_object* v___x_926_; 
v___x_926_ = lean_box(0);
return v___x_926_;
}
else
{
lean_object* v_key_927_; lean_object* v_value_928_; lean_object* v_tail_929_; uint8_t v___x_930_; 
v_key_927_ = lean_ctor_get(v_x_925_, 0);
v_value_928_ = lean_ctor_get(v_x_925_, 1);
v_tail_929_ = lean_ctor_get(v_x_925_, 2);
v___x_930_ = l_Lean_instBEqFVarId_beq(v_key_927_, v_a_924_);
if (v___x_930_ == 0)
{
v_x_925_ = v_tail_929_;
goto _start;
}
else
{
lean_object* v___x_932_; 
lean_inc(v_value_928_);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v_value_928_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_933_, v_x_934_);
lean_dec(v_x_934_);
lean_dec(v_a_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object* v_m_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_buckets_938_; lean_object* v___x_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v_fold_943_; uint64_t v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_buckets_938_ = lean_ctor_get(v_m_936_, 1);
v___x_939_ = lean_array_get_size(v_buckets_938_);
v___x_940_ = l_Lean_instHashableFVarId_hash(v_a_937_);
v___x_941_ = 32ULL;
v___x_942_ = lean_uint64_shift_right(v___x_940_, v___x_941_);
v_fold_943_ = lean_uint64_xor(v___x_940_, v___x_942_);
v___x_944_ = 16ULL;
v___x_945_ = lean_uint64_shift_right(v_fold_943_, v___x_944_);
v___x_946_ = lean_uint64_xor(v_fold_943_, v___x_945_);
v___x_947_ = lean_uint64_to_usize(v___x_946_);
v___x_948_ = lean_usize_of_nat(v___x_939_);
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_sub(v___x_948_, v___x_949_);
v___x_951_ = lean_usize_land(v___x_947_, v___x_950_);
v___x_952_ = lean_array_uget_borrowed(v_buckets_938_, v___x_951_);
v___x_953_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_937_, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object* v_m_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_m_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* v_plannedDecision_957_, lean_object* v_var_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_st_ref_get(v_a_959_);
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_961_, v_var_958_);
lean_dec(v___x_961_);
if (lean_obj_tag(v___x_962_) == 1)
{
lean_object* v_val_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_987_; 
v_val_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_987_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_987_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_val_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_987_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
if (lean_obj_tag(v_val_963_) == 3)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_967_ = lean_st_ref_take(v_a_959_);
v___x_968_ = lean_box(0);
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_967_, v_var_958_, v_plannedDecision_957_);
v___x_970_ = lean_st_ref_put(v_a_959_, v___x_969_);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 0);
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_972_ = v___x_965_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_968_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_963_, v_plannedDecision_957_);
lean_dec(v_plannedDecision_957_);
lean_dec(v_val_963_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_975_ = lean_st_ref_take(v_a_959_);
v___x_976_ = lean_box(0);
v___x_977_ = lean_box(2);
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_975_, v_var_958_, v___x_977_);
v___x_979_ = lean_st_ref_put(v_a_959_, v___x_978_);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 0);
lean_ctor_set(v___x_965_, 0, v___x_976_);
v___x_981_ = v___x_965_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_985_; 
lean_dec(v_var_958_);
v___x_983_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 0);
lean_ctor_set(v___x_965_, 0, v___x_983_);
v___x_985_ = v___x_965_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v___x_962_);
lean_dec(v_var_958_);
lean_dec(v_plannedDecision_957_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_990_, lean_object* v_var_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_990_, v_var_991_, v_a_992_);
lean_dec(v_a_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_995_, lean_object* v_var_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_995_, v_var_996_, v_a_997_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_1005_, lean_object* v_var_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1005_, v_var_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec(v_a_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_1015_, lean_object* v_m_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1016_, v_a_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1019_, lean_object* v_m_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1019_, v_m_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_m_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object* v_00_u03b2_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_1024_, v_a_1025_, v_b_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object* v_00_u03b2_1028_, lean_object* v_a_1029_, lean_object* v_x_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_1029_, v_x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1032_, lean_object* v_a_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_1032_, v_a_1033_, v_x_1034_);
lean_dec(v_x_1034_);
lean_dec(v_a_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object* v_00_u03b2_1036_, lean_object* v_a_1037_, lean_object* v_b_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_1037_, v_b_1038_, v_x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1041_, lean_object* v_f_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
switch(lean_obj_tag(v_alt_1041_))
{
case 0:
{
lean_object* v_code_1050_; lean_object* v___x_1051_; 
v_code_1050_ = lean_ctor_get(v_alt_1041_, 2);
lean_inc_ref(v_code_1050_);
lean_dec_ref_known(v_alt_1041_, 3);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc(v___y_1043_);
v___x_1051_ = lean_apply_8(v_f_1042_, v_code_1050_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
return v___x_1051_;
}
case 1:
{
lean_object* v_code_1052_; lean_object* v___x_1053_; 
v_code_1052_ = lean_ctor_get(v_alt_1041_, 1);
lean_inc_ref(v_code_1052_);
lean_dec_ref_known(v_alt_1041_, 2);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc(v___y_1043_);
v___x_1053_ = lean_apply_8(v_f_1042_, v_code_1052_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
return v___x_1053_;
}
default: 
{
lean_object* v_code_1054_; lean_object* v___x_1055_; 
v_code_1054_ = lean_ctor_get(v_alt_1041_, 0);
lean_inc_ref(v_code_1054_);
lean_dec_ref_known(v_alt_1041_, 1);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc(v___y_1043_);
v___x_1055_ = lean_apply_8(v_f_1042_, v_code_1054_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1056_, lean_object* v_f_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1056_, v_f_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
return v_res_1065_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_instMonadEIO___redArg();
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_toApplicative_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1144_; 
v___x_1079_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1080_ = l_StateRefT_x27_instMonad___redArg(v___x_1079_);
v_toApplicative_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1080_, 1);
lean_dec(v_unused_1145_);
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1144_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_toApplicative_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1144_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_toFunctor_1085_; lean_object* v_toSeq_1086_; lean_object* v_toSeqLeft_1087_; lean_object* v_toSeqRight_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1142_; 
v_toFunctor_1085_ = lean_ctor_get(v_toApplicative_1081_, 0);
v_toSeq_1086_ = lean_ctor_get(v_toApplicative_1081_, 2);
v_toSeqLeft_1087_ = lean_ctor_get(v_toApplicative_1081_, 3);
v_toSeqRight_1088_ = lean_ctor_get(v_toApplicative_1081_, 4);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_toApplicative_1081_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v_toApplicative_1081_, 1);
lean_dec(v_unused_1143_);
v___x_1090_ = v_toApplicative_1081_;
v_isShared_1091_ = v_isSharedCheck_1142_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_toSeqRight_1088_);
lean_inc(v_toSeqLeft_1087_);
lean_inc(v_toSeq_1086_);
lean_inc(v_toFunctor_1085_);
lean_dec(v_toApplicative_1081_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1142_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___f_1099_; lean_object* v___x_1101_; 
v___f_1092_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1093_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1085_);
v___f_1094_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1094_, 0, v_toFunctor_1085_);
v___f_1095_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1095_, 0, v_toFunctor_1085_);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___f_1094_);
lean_ctor_set(v___x_1096_, 1, v___f_1095_);
v___f_1097_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1097_, 0, v_toSeqRight_1088_);
v___f_1098_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1098_, 0, v_toSeqLeft_1087_);
v___f_1099_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1099_, 0, v_toSeq_1086_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v___f_1097_);
lean_ctor_set(v___x_1090_, 3, v___f_1098_);
lean_ctor_set(v___x_1090_, 2, v___f_1099_);
lean_ctor_set(v___x_1090_, 1, v___f_1092_);
lean_ctor_set(v___x_1090_, 0, v___x_1096_);
v___x_1101_ = v___x_1090_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___f_1092_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v___f_1099_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v___f_1098_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v___f_1097_);
v___x_1101_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___f_1093_);
lean_ctor_set(v___x_1083_, 0, v___x_1101_);
v___x_1103_ = v___x_1083_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___f_1093_);
v___x_1103_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v_toApplicative_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1138_; 
v___x_1104_ = l_StateRefT_x27_instMonad___redArg(v___x_1103_);
v_toApplicative_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1104_, 1);
lean_dec(v_unused_1139_);
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1138_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_toApplicative_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1138_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_toFunctor_1109_; lean_object* v_toSeq_1110_; lean_object* v_toSeqLeft_1111_; lean_object* v_toSeqRight_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1136_; 
v_toFunctor_1109_ = lean_ctor_get(v_toApplicative_1105_, 0);
v_toSeq_1110_ = lean_ctor_get(v_toApplicative_1105_, 2);
v_toSeqLeft_1111_ = lean_ctor_get(v_toApplicative_1105_, 3);
v_toSeqRight_1112_ = lean_ctor_get(v_toApplicative_1105_, 4);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_toApplicative_1105_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_toApplicative_1105_, 1);
lean_dec(v_unused_1137_);
v___x_1114_ = v_toApplicative_1105_;
v_isShared_1115_ = v_isSharedCheck_1136_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_toSeqRight_1112_);
lean_inc(v_toSeqLeft_1111_);
lean_inc(v_toSeq_1110_);
lean_inc(v_toFunctor_1109_);
lean_dec(v_toApplicative_1105_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1136_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___x_1125_; 
v___f_1116_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1117_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1109_);
v___f_1118_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1118_, 0, v_toFunctor_1109_);
v___f_1119_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1119_, 0, v_toFunctor_1109_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___f_1118_);
lean_ctor_set(v___x_1120_, 1, v___f_1119_);
v___f_1121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1121_, 0, v_toSeqRight_1112_);
v___f_1122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1122_, 0, v_toSeqLeft_1111_);
v___f_1123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1123_, 0, v_toSeq_1110_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___f_1121_);
lean_ctor_set(v___x_1114_, 3, v___f_1122_);
lean_ctor_set(v___x_1114_, 2, v___f_1123_);
lean_ctor_set(v___x_1114_, 1, v___f_1116_);
lean_ctor_set(v___x_1114_, 0, v___x_1120_);
v___x_1125_ = v___x_1114_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___f_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___f_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v___f_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v___f_1121_);
v___x_1125_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v___f_1117_);
lean_ctor_set(v___x_1107_, 0, v___x_1125_);
v___x_1127_ = v___x_1107_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___f_1117_);
v___x_1127_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_8045__overap_1132_; lean_object* v___x_1133_; 
v___x_1128_ = l_ReaderT_instMonad___redArg(v___x_1127_);
v___x_1129_ = l_StateRefT_x27_instMonad___redArg(v___x_1128_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_instInhabitedOfMonad___redArg(v___x_1129_, v___x_1130_);
v___x_8045__overap_1132_ = lean_panic_fn_borrowed(v___x_1131_, v_msg_1071_);
lean_dec(v___x_1131_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc(v___y_1072_);
v___x_1133_ = lean_apply_7(v___x_8045__overap_1132_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
return v___x_1133_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec(v___y_1147_);
return v_res_1154_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1158_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1159_ = lean_unsigned_to_nat(40u);
v___x_1160_ = lean_unsigned_to_nat(49u);
v___x_1161_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1162_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1163_ = l_mkPanicMessageWithDecl(v___x_1162_, v___x_1161_, v___x_1160_, v___x_1159_, v___x_1158_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1164_, lean_object* v_e_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_ty_1174_; lean_object* v_body_1175_; uint8_t v___x_1178_; 
v___x_1178_ = l_Lean_Expr_hasFVar(v_e_1165_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_e_1165_);
lean_dec_ref(v_f_1164_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
else
{
switch(lean_obj_tag(v_e_1165_))
{
case 1:
{
lean_object* v_fvarId_1181_; lean_object* v___x_1182_; 
v_fvarId_1181_ = lean_ctor_get(v_e_1165_, 0);
lean_inc(v_fvarId_1181_);
lean_dec_ref_known(v_e_1165_, 1);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc(v___y_1166_);
v___x_1182_ = lean_apply_8(v_f_1164_, v_fvarId_1181_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, lean_box(0));
return v___x_1182_;
}
case 2:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec_ref_known(v_e_1165_, 1);
lean_dec_ref(v_f_1164_);
v___x_1183_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1184_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1183_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1184_;
}
case 5:
{
lean_object* v_fn_1185_; lean_object* v_arg_1186_; lean_object* v___x_1187_; 
v_fn_1185_ = lean_ctor_get(v_e_1165_, 0);
lean_inc_ref(v_fn_1185_);
v_arg_1186_ = lean_ctor_get(v_e_1165_, 1);
lean_inc_ref(v_arg_1186_);
lean_dec_ref_known(v_e_1165_, 2);
lean_inc_ref(v_f_1164_);
v___x_1187_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1164_, v_fn_1185_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_dec_ref_known(v___x_1187_, 1);
v_e_1165_ = v_arg_1186_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1186_);
lean_dec_ref(v_f_1164_);
return v___x_1187_;
}
}
case 6:
{
lean_object* v_binderType_1189_; lean_object* v_body_1190_; 
v_binderType_1189_ = lean_ctor_get(v_e_1165_, 1);
lean_inc_ref(v_binderType_1189_);
v_body_1190_ = lean_ctor_get(v_e_1165_, 2);
lean_inc_ref(v_body_1190_);
lean_dec_ref_known(v_e_1165_, 3);
v_ty_1174_ = v_binderType_1189_;
v_body_1175_ = v_body_1190_;
goto v___jp_1173_;
}
case 7:
{
lean_object* v_binderType_1191_; lean_object* v_body_1192_; 
v_binderType_1191_ = lean_ctor_get(v_e_1165_, 1);
lean_inc_ref(v_binderType_1191_);
v_body_1192_ = lean_ctor_get(v_e_1165_, 2);
lean_inc_ref(v_body_1192_);
lean_dec_ref_known(v_e_1165_, 3);
v_ty_1174_ = v_binderType_1191_;
v_body_1175_ = v_body_1192_;
goto v___jp_1173_;
}
case 8:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref_known(v_e_1165_, 4);
lean_dec_ref(v_f_1164_);
v___x_1193_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1194_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1193_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1194_;
}
case 11:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref_known(v_e_1165_, 3);
lean_dec_ref(v_f_1164_);
v___x_1195_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1196_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1195_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1196_;
}
default: 
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v_e_1165_);
lean_dec_ref(v_f_1164_);
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
v___jp_1173_:
{
lean_object* v___x_1176_; 
lean_inc_ref(v_f_1164_);
v___x_1176_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1164_, v_ty_1174_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_dec_ref_known(v___x_1176_, 1);
v_e_1165_ = v_body_1175_;
goto _start;
}
else
{
lean_dec_ref(v_body_1175_);
lean_dec_ref(v_f_1164_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1199_, lean_object* v_e_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1199_, v_e_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec(v___y_1201_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1209_, lean_object* v_param_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_type_1218_; lean_object* v___x_1219_; 
v_type_1218_ = lean_ctor_get(v_param_1210_, 2);
lean_inc_ref(v_type_1218_);
lean_dec_ref(v_param_1210_);
v___x_1219_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1209_, v_type_1218_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1220_, lean_object* v_param_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1220_, v_param_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1230_, lean_object* v_f_1231_, lean_object* v_as_1232_, size_t v_i_1233_, size_t v_stop_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_usize_dec_eq(v_i_1233_, v_stop_1234_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_array_uget_borrowed(v_as_1232_, v_i_1233_);
lean_inc(v___x_1244_);
lean_inc_ref(v_f_1231_);
v___x_1245_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1231_, v___x_1244_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; size_t v___x_1247_; size_t v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1233_, v___x_1247_);
v_i_1233_ = v___x_1248_;
v_b_1235_ = v_a_1246_;
goto _start;
}
else
{
lean_dec_ref(v_f_1231_);
return v___x_1245_;
}
}
else
{
lean_object* v___x_1250_; 
lean_dec_ref(v_f_1231_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_b_1235_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1251_, lean_object* v_f_1252_, lean_object* v_as_1253_, lean_object* v_i_1254_, lean_object* v_stop_1255_, lean_object* v_b_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_pu_boxed_1264_; size_t v_i_boxed_1265_; size_t v_stop_boxed_1266_; lean_object* v_res_1267_; 
v_pu_boxed_1264_ = lean_unbox(v_pu_1251_);
v_i_boxed_1265_ = lean_unbox_usize(v_i_1254_);
lean_dec(v_i_1254_);
v_stop_boxed_1266_ = lean_unbox_usize(v_stop_1255_);
lean_dec(v_stop_1255_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1264_, v_f_1252_, v_as_1253_, v_i_boxed_1265_, v_stop_boxed_1266_, v_b_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v_as_1253_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1268_, lean_object* v_arg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
switch(lean_obj_tag(v_arg_1269_))
{
case 0:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_f_1268_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
case 1:
{
lean_object* v_fvarId_1279_; lean_object* v___x_1280_; 
v_fvarId_1279_ = lean_ctor_get(v_arg_1269_, 0);
lean_inc(v_fvarId_1279_);
lean_dec_ref_known(v_arg_1269_, 1);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc(v___y_1270_);
v___x_1280_ = lean_apply_8(v_f_1268_, v_fvarId_1279_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, lean_box(0));
return v___x_1280_;
}
default: 
{
lean_object* v_expr_1281_; lean_object* v___x_1282_; 
v_expr_1281_ = lean_ctor_get(v_arg_1269_, 0);
lean_inc_ref(v_expr_1281_);
lean_dec_ref_known(v_arg_1269_, 1);
v___x_1282_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1268_, v_expr_1281_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1283_, lean_object* v_arg_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1283_, v_arg_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1293_, lean_object* v_f_1294_, lean_object* v_as_1295_, size_t v_i_1296_, size_t v_stop_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_eq(v_i_1296_, v_stop_1297_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_array_uget_borrowed(v_as_1295_, v_i_1296_);
lean_inc(v___x_1307_);
lean_inc_ref(v_f_1294_);
v___x_1308_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1294_, v___x_1307_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; size_t v___x_1310_; size_t v___x_1311_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_add(v_i_1296_, v___x_1310_);
v_i_1296_ = v___x_1311_;
v_b_1298_ = v_a_1309_;
goto _start;
}
else
{
lean_dec_ref(v_f_1294_);
return v___x_1308_;
}
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v_f_1294_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_b_1298_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1314_, lean_object* v_f_1315_, lean_object* v_as_1316_, lean_object* v_i_1317_, lean_object* v_stop_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v_pu_boxed_1327_; size_t v_i_boxed_1328_; size_t v_stop_boxed_1329_; lean_object* v_res_1330_; 
v_pu_boxed_1327_ = lean_unbox(v_pu_1314_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_stop_boxed_1329_ = lean_unbox_usize(v_stop_1318_);
lean_dec(v_stop_1318_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1327_, v_f_1315_, v_as_1316_, v_i_boxed_1328_, v_stop_boxed_1329_, v_b_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v_as_1316_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1331_, lean_object* v_f_1332_, lean_object* v_e_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_args_1342_; 
switch(lean_obj_tag(v_e_1333_))
{
case 2:
{
lean_object* v_struct_1351_; lean_object* v___x_1352_; 
v_struct_1351_ = lean_ctor_get(v_e_1333_, 2);
lean_inc(v_struct_1351_);
lean_dec_ref_known(v_e_1333_, 3);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1352_ = lean_apply_8(v_f_1332_, v_struct_1351_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1352_;
}
case 3:
{
lean_object* v_args_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_args_1353_ = lean_ctor_get(v_e_1333_, 2);
lean_inc_ref(v_args_1353_);
lean_dec_ref_known(v_e_1333_, 3);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_array_get_size(v_args_1353_);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_nat_dec_lt(v___x_1354_, v___x_1355_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v_args_1353_);
lean_dec_ref(v_f_1332_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
return v___x_1358_;
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1355_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1331_, v_f_1332_, v_args_1353_, v___x_1359_, v___x_1360_, v___x_1356_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v_args_1353_);
return v___x_1361_;
}
}
case 4:
{
lean_object* v_fvarId_1362_; lean_object* v_args_1363_; lean_object* v___x_1364_; 
v_fvarId_1362_ = lean_ctor_get(v_e_1333_, 0);
lean_inc(v_fvarId_1362_);
v_args_1363_ = lean_ctor_get(v_e_1333_, 1);
lean_inc_ref(v_args_1363_);
lean_dec_ref_known(v_e_1333_, 2);
lean_inc_ref(v_f_1332_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1364_ = lean_apply_8(v_f_1332_, v_fvarId_1362_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1364_, 0);
lean_dec(v_unused_1379_);
v___x_1366_ = v___x_1364_;
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v___x_1364_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_array_get_size(v_args_1363_);
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_nat_dec_lt(v___x_1368_, v___x_1369_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1373_; 
lean_dec_ref(v_args_1363_);
lean_dec_ref(v_f_1332_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
lean_del_object(v___x_1366_);
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1369_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1331_, v_f_1332_, v_args_1363_, v___x_1375_, v___x_1376_, v___x_1370_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v_args_1363_);
return v___x_1377_;
}
}
}
else
{
lean_dec_ref(v_args_1363_);
lean_dec_ref(v_f_1332_);
return v___x_1364_;
}
}
case 5:
{
lean_object* v_args_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_args_1380_ = lean_ctor_get(v_e_1333_, 1);
lean_inc_ref(v_args_1380_);
lean_dec_ref_known(v_e_1333_, 2);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_array_get_size(v_args_1380_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_nat_dec_lt(v___x_1381_, v___x_1382_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec_ref(v_args_1380_);
lean_dec_ref(v_f_1332_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
return v___x_1385_;
}
else
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = lean_usize_of_nat(v___x_1382_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1331_, v_f_1332_, v_args_1380_, v___x_1386_, v___x_1387_, v___x_1383_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v_args_1380_);
return v___x_1388_;
}
}
case 6:
{
lean_object* v_var_1389_; lean_object* v___x_1390_; 
v_var_1389_ = lean_ctor_get(v_e_1333_, 1);
lean_inc(v_var_1389_);
lean_dec_ref_known(v_e_1333_, 2);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1390_ = lean_apply_8(v_f_1332_, v_var_1389_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1390_;
}
case 7:
{
lean_object* v_var_1391_; lean_object* v___x_1392_; 
v_var_1391_ = lean_ctor_get(v_e_1333_, 1);
lean_inc(v_var_1391_);
lean_dec_ref_known(v_e_1333_, 2);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1392_ = lean_apply_8(v_f_1332_, v_var_1391_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1392_;
}
case 8:
{
lean_object* v_var_1393_; lean_object* v___x_1394_; 
v_var_1393_ = lean_ctor_get(v_e_1333_, 2);
lean_inc(v_var_1393_);
lean_dec_ref_known(v_e_1333_, 3);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1394_ = lean_apply_8(v_f_1332_, v_var_1393_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1394_;
}
case 9:
{
lean_object* v_args_1395_; 
v_args_1395_ = lean_ctor_get(v_e_1333_, 1);
lean_inc_ref(v_args_1395_);
lean_dec_ref_known(v_e_1333_, 2);
v_args_1342_ = v_args_1395_;
goto v___jp_1341_;
}
case 10:
{
lean_object* v_args_1396_; 
v_args_1396_ = lean_ctor_get(v_e_1333_, 1);
lean_inc_ref(v_args_1396_);
lean_dec_ref_known(v_e_1333_, 2);
v_args_1342_ = v_args_1396_;
goto v___jp_1341_;
}
case 11:
{
lean_object* v_var_1397_; lean_object* v___x_1398_; 
v_var_1397_ = lean_ctor_get(v_e_1333_, 1);
lean_inc(v_var_1397_);
lean_dec_ref_known(v_e_1333_, 2);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1398_ = lean_apply_8(v_f_1332_, v_var_1397_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1398_;
}
case 12:
{
lean_object* v_var_1399_; lean_object* v_args_1400_; lean_object* v___x_1401_; 
v_var_1399_ = lean_ctor_get(v_e_1333_, 0);
lean_inc(v_var_1399_);
v_args_1400_ = lean_ctor_get(v_e_1333_, 2);
lean_inc_ref(v_args_1400_);
lean_dec_ref_known(v_e_1333_, 3);
lean_inc_ref(v_f_1332_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1401_ = lean_apply_8(v_f_1332_, v_var_1399_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1415_; 
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1416_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1415_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1415_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_array_get_size(v_args_1400_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_nat_dec_lt(v___x_1405_, v___x_1406_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1410_; 
lean_dec_ref(v_args_1400_);
lean_dec_ref(v_f_1332_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1410_ = v___x_1403_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1407_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
lean_del_object(v___x_1403_);
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_of_nat(v___x_1406_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1331_, v_f_1332_, v_args_1400_, v___x_1412_, v___x_1413_, v___x_1407_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v_args_1400_);
return v___x_1414_;
}
}
}
else
{
lean_dec_ref(v_args_1400_);
lean_dec_ref(v_f_1332_);
return v___x_1401_;
}
}
case 13:
{
lean_object* v_fvarId_1417_; lean_object* v___x_1418_; 
v_fvarId_1417_ = lean_ctor_get(v_e_1333_, 1);
lean_inc(v_fvarId_1417_);
lean_dec_ref_known(v_e_1333_, 2);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1418_ = lean_apply_8(v_f_1332_, v_fvarId_1417_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1418_;
}
case 14:
{
lean_object* v_fvarId_1419_; lean_object* v___x_1420_; 
v_fvarId_1419_ = lean_ctor_get(v_e_1333_, 0);
lean_inc(v_fvarId_1419_);
lean_dec_ref_known(v_e_1333_, 1);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1420_ = lean_apply_8(v_f_1332_, v_fvarId_1419_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1420_;
}
case 15:
{
lean_object* v_fvarId_1421_; lean_object* v___x_1422_; 
v_fvarId_1421_ = lean_ctor_get(v_e_1333_, 0);
lean_inc(v_fvarId_1421_);
lean_dec_ref_known(v_e_1333_, 1);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___y_1334_);
v___x_1422_ = lean_apply_8(v_f_1332_, v_fvarId_1421_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
return v___x_1422_;
}
default: 
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec(v_e_1333_);
lean_dec_ref(v_f_1332_);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
v___jp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_array_get_size(v_args_1342_);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_nat_dec_lt(v___x_1343_, v___x_1344_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref(v_args_1342_);
lean_dec_ref(v_f_1332_);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
return v___x_1347_;
}
else
{
size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1344_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1331_, v_f_1332_, v_args_1342_, v___x_1348_, v___x_1349_, v___x_1345_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v_args_1342_);
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1425_, lean_object* v_f_1426_, lean_object* v_e_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v_pu_boxed_1435_; lean_object* v_res_1436_; 
v_pu_boxed_1435_ = lean_unbox(v_pu_1425_);
v_res_1436_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1435_, v_f_1426_, v_e_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec(v___y_1428_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1437_, lean_object* v_f_1438_, lean_object* v_decl_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_type_1447_; lean_object* v_value_1448_; lean_object* v___x_1449_; 
v_type_1447_ = lean_ctor_get(v_decl_1439_, 2);
lean_inc_ref(v_type_1447_);
v_value_1448_ = lean_ctor_get(v_decl_1439_, 3);
lean_inc(v_value_1448_);
lean_dec_ref(v_decl_1439_);
lean_inc_ref(v_f_1438_);
v___x_1449_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1438_, v_type_1447_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref_known(v___x_1449_, 1);
v___x_1450_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1437_, v_f_1438_, v_value_1448_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1450_;
}
else
{
lean_dec(v_value_1448_);
lean_dec_ref(v_f_1438_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1451_, lean_object* v_f_1452_, lean_object* v_decl_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_pu_boxed_1461_; lean_object* v_res_1462_; 
v_pu_boxed_1461_ = lean_unbox(v_pu_1451_);
v_res_1462_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1461_, v_f_1452_, v_decl_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec(v___y_1454_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1463_, lean_object* v_f_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v_pu_boxed_1473_; lean_object* v_res_1474_; 
v_pu_boxed_1473_ = lean_unbox(v_pu_1463_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1473_, v_f_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v___y_1466_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1475_, lean_object* v_f_1476_, lean_object* v_as_1477_, size_t v_i_1478_, size_t v_stop_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_usize_dec_eq(v_i_1478_, v_stop_1479_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_box(v_pu_1475_);
lean_inc_ref(v_f_1476_);
v___f_1490_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1490_, 0, v___x_1489_);
lean_closure_set(v___f_1490_, 1, v_f_1476_);
v___x_1491_ = lean_array_uget_borrowed(v_as_1477_, v_i_1478_);
lean_inc(v___x_1491_);
v___x_1492_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1491_, v___f_1490_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; size_t v___x_1494_; size_t v___x_1495_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = ((size_t)1ULL);
v___x_1495_ = lean_usize_add(v_i_1478_, v___x_1494_);
v_i_1478_ = v___x_1495_;
v_b_1480_ = v_a_1493_;
goto _start;
}
else
{
lean_dec_ref(v_f_1476_);
return v___x_1492_;
}
}
else
{
lean_object* v___x_1497_; 
lean_dec_ref(v_f_1476_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1480_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1498_, lean_object* v_f_1499_, lean_object* v_c_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
switch(lean_obj_tag(v_c_1500_))
{
case 0:
{
lean_object* v_decl_1508_; lean_object* v_k_1509_; lean_object* v___x_1510_; 
v_decl_1508_ = lean_ctor_get(v_c_1500_, 0);
lean_inc_ref(v_decl_1508_);
v_k_1509_ = lean_ctor_get(v_c_1500_, 1);
lean_inc_ref(v_k_1509_);
lean_dec_ref_known(v_c_1500_, 2);
lean_inc_ref(v_f_1499_);
v___x_1510_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1498_, v_f_1499_, v_decl_1508_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec_ref_known(v___x_1510_, 1);
v_c_1500_ = v_k_1509_;
goto _start;
}
else
{
lean_dec_ref(v_k_1509_);
lean_dec_ref(v_f_1499_);
return v___x_1510_;
}
}
case 3:
{
lean_object* v_fvarId_1512_; lean_object* v_args_1513_; lean_object* v___x_1514_; 
v_fvarId_1512_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1512_);
v_args_1513_ = lean_ctor_get(v_c_1500_, 1);
lean_inc_ref(v_args_1513_);
lean_dec_ref_known(v_c_1500_, 2);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1514_ = lean_apply_8(v_f_1499_, v_fvarId_1512_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1528_; 
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1514_, 0);
lean_dec(v_unused_1529_);
v___x_1516_ = v___x_1514_;
v_isShared_1517_ = v_isSharedCheck_1528_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v___x_1514_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1528_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_array_get_size(v_args_1513_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_nat_dec_lt(v___x_1518_, v___x_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1523_; 
lean_dec_ref(v_args_1513_);
lean_dec_ref(v_f_1499_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1520_);
v___x_1523_ = v___x_1516_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1520_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
lean_del_object(v___x_1516_);
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1519_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1498_, v_f_1499_, v_args_1513_, v___x_1525_, v___x_1526_, v___x_1520_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec_ref(v_args_1513_);
return v___x_1527_;
}
}
}
else
{
lean_dec_ref(v_args_1513_);
lean_dec_ref(v_f_1499_);
return v___x_1514_;
}
}
case 4:
{
lean_object* v_cases_1530_; lean_object* v_resultType_1531_; lean_object* v_discr_1532_; lean_object* v_alts_1533_; lean_object* v___x_1534_; 
v_cases_1530_ = lean_ctor_get(v_c_1500_, 0);
lean_inc_ref(v_cases_1530_);
lean_dec_ref_known(v_c_1500_, 1);
v_resultType_1531_ = lean_ctor_get(v_cases_1530_, 1);
lean_inc_ref(v_resultType_1531_);
v_discr_1532_ = lean_ctor_get(v_cases_1530_, 2);
lean_inc(v_discr_1532_);
v_alts_1533_ = lean_ctor_get(v_cases_1530_, 3);
lean_inc_ref(v_alts_1533_);
lean_dec_ref(v_cases_1530_);
lean_inc_ref(v_f_1499_);
v___x_1534_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1499_, v_resultType_1531_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref_known(v___x_1534_, 1);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1535_ = lean_apply_8(v_f_1499_, v_discr_1532_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1549_; 
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1535_, 0);
lean_dec(v_unused_1550_);
v___x_1537_ = v___x_1535_;
v_isShared_1538_ = v_isSharedCheck_1549_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v___x_1535_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1549_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = lean_array_get_size(v_alts_1533_);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_nat_dec_lt(v___x_1539_, v___x_1540_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1544_; 
lean_dec_ref(v_alts_1533_);
lean_dec_ref(v_f_1499_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1541_);
v___x_1544_ = v___x_1537_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1541_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
else
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
lean_del_object(v___x_1537_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = lean_usize_of_nat(v___x_1540_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1498_, v_f_1499_, v_alts_1533_, v___x_1546_, v___x_1547_, v___x_1541_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec_ref(v_alts_1533_);
return v___x_1548_;
}
}
}
else
{
lean_dec_ref(v_alts_1533_);
lean_dec_ref(v_f_1499_);
return v___x_1535_;
}
}
else
{
lean_dec_ref(v_alts_1533_);
lean_dec(v_discr_1532_);
lean_dec_ref(v_f_1499_);
return v___x_1534_;
}
}
case 5:
{
lean_object* v_fvarId_1551_; lean_object* v___x_1552_; 
v_fvarId_1551_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1551_);
lean_dec_ref_known(v_c_1500_, 1);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1552_ = lean_apply_8(v_f_1499_, v_fvarId_1551_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
return v___x_1552_;
}
case 6:
{
lean_object* v_type_1553_; lean_object* v___x_1554_; 
v_type_1553_ = lean_ctor_get(v_c_1500_, 0);
lean_inc_ref(v_type_1553_);
lean_dec_ref_known(v_c_1500_, 1);
v___x_1554_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1499_, v_type_1553_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1554_;
}
case 7:
{
lean_object* v_fvarId_1555_; lean_object* v_y_1556_; lean_object* v_k_1557_; lean_object* v___x_1558_; 
v_fvarId_1555_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1555_);
v_y_1556_ = lean_ctor_get(v_c_1500_, 2);
lean_inc(v_y_1556_);
v_k_1557_ = lean_ctor_get(v_c_1500_, 3);
lean_inc_ref(v_k_1557_);
lean_dec_ref_known(v_c_1500_, 4);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1558_ = lean_apply_8(v_f_1499_, v_fvarId_1555_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; 
lean_dec_ref_known(v___x_1558_, 1);
lean_inc_ref(v_f_1499_);
v___x_1559_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1499_, v_y_1556_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec_ref_known(v___x_1559_, 1);
v_c_1500_ = v_k_1557_;
goto _start;
}
else
{
lean_dec_ref(v_k_1557_);
lean_dec_ref(v_f_1499_);
return v___x_1559_;
}
}
else
{
lean_dec_ref(v_k_1557_);
lean_dec(v_y_1556_);
lean_dec_ref(v_f_1499_);
return v___x_1558_;
}
}
case 8:
{
lean_object* v_fvarId_1561_; lean_object* v_y_1562_; lean_object* v_k_1563_; lean_object* v___x_1564_; 
v_fvarId_1561_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1561_);
v_y_1562_ = lean_ctor_get(v_c_1500_, 2);
lean_inc(v_y_1562_);
v_k_1563_ = lean_ctor_get(v_c_1500_, 3);
lean_inc_ref(v_k_1563_);
lean_dec_ref_known(v_c_1500_, 4);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1564_ = lean_apply_8(v_f_1499_, v_fvarId_1561_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v___x_1564_, 1);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1565_ = lean_apply_8(v_f_1499_, v_y_1562_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref_known(v___x_1565_, 1);
v_c_1500_ = v_k_1563_;
goto _start;
}
else
{
lean_dec_ref(v_k_1563_);
lean_dec_ref(v_f_1499_);
return v___x_1565_;
}
}
else
{
lean_dec_ref(v_k_1563_);
lean_dec(v_y_1562_);
lean_dec_ref(v_f_1499_);
return v___x_1564_;
}
}
case 9:
{
lean_object* v_fvarId_1567_; lean_object* v_y_1568_; lean_object* v_ty_1569_; lean_object* v_k_1570_; lean_object* v___x_1571_; 
v_fvarId_1567_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1567_);
v_y_1568_ = lean_ctor_get(v_c_1500_, 3);
lean_inc(v_y_1568_);
v_ty_1569_ = lean_ctor_get(v_c_1500_, 4);
lean_inc_ref(v_ty_1569_);
v_k_1570_ = lean_ctor_get(v_c_1500_, 5);
lean_inc_ref(v_k_1570_);
lean_dec_ref_known(v_c_1500_, 6);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1571_ = lean_apply_8(v_f_1499_, v_fvarId_1567_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref_known(v___x_1571_, 1);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1572_ = lean_apply_8(v_f_1499_, v_y_1568_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1572_, 1);
lean_inc_ref(v_f_1499_);
v___x_1573_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1499_, v_ty_1569_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_dec_ref_known(v___x_1573_, 1);
v_c_1500_ = v_k_1570_;
goto _start;
}
else
{
lean_dec_ref(v_k_1570_);
lean_dec_ref(v_f_1499_);
return v___x_1573_;
}
}
else
{
lean_dec_ref(v_k_1570_);
lean_dec_ref(v_ty_1569_);
lean_dec_ref(v_f_1499_);
return v___x_1572_;
}
}
else
{
lean_dec_ref(v_k_1570_);
lean_dec_ref(v_ty_1569_);
lean_dec(v_y_1568_);
lean_dec_ref(v_f_1499_);
return v___x_1571_;
}
}
case 10:
{
lean_object* v_fvarId_1575_; lean_object* v_k_1576_; lean_object* v___x_1577_; 
v_fvarId_1575_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1575_);
v_k_1576_ = lean_ctor_get(v_c_1500_, 2);
lean_inc_ref(v_k_1576_);
lean_dec_ref_known(v_c_1500_, 3);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1577_ = lean_apply_8(v_f_1499_, v_fvarId_1575_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_dec_ref_known(v___x_1577_, 1);
v_c_1500_ = v_k_1576_;
goto _start;
}
else
{
lean_dec_ref(v_k_1576_);
lean_dec_ref(v_f_1499_);
return v___x_1577_;
}
}
case 11:
{
lean_object* v_fvarId_1579_; lean_object* v_k_1580_; lean_object* v___x_1581_; 
v_fvarId_1579_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1579_);
v_k_1580_ = lean_ctor_get(v_c_1500_, 2);
lean_inc_ref(v_k_1580_);
lean_dec_ref_known(v_c_1500_, 3);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1581_ = lean_apply_8(v_f_1499_, v_fvarId_1579_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v_c_1500_ = v_k_1580_;
goto _start;
}
else
{
lean_dec_ref(v_k_1580_);
lean_dec_ref(v_f_1499_);
return v___x_1581_;
}
}
case 12:
{
lean_object* v_fvarId_1583_; lean_object* v_k_1584_; lean_object* v___x_1585_; 
v_fvarId_1583_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1583_);
v_k_1584_ = lean_ctor_get(v_c_1500_, 3);
lean_inc_ref(v_k_1584_);
lean_dec_ref_known(v_c_1500_, 4);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1585_ = lean_apply_8(v_f_1499_, v_fvarId_1583_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_dec_ref_known(v___x_1585_, 1);
v_c_1500_ = v_k_1584_;
goto _start;
}
else
{
lean_dec_ref(v_k_1584_);
lean_dec_ref(v_f_1499_);
return v___x_1585_;
}
}
case 13:
{
lean_object* v_fvarId_1587_; lean_object* v_k_1588_; lean_object* v___x_1589_; 
v_fvarId_1587_ = lean_ctor_get(v_c_1500_, 0);
lean_inc(v_fvarId_1587_);
v_k_1588_ = lean_ctor_get(v_c_1500_, 1);
lean_inc_ref(v_k_1588_);
lean_dec_ref_known(v_c_1500_, 2);
lean_inc_ref(v_f_1499_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1589_ = lean_apply_8(v_f_1499_, v_fvarId_1587_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, lean_box(0));
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_dec_ref_known(v___x_1589_, 1);
v_c_1500_ = v_k_1588_;
goto _start;
}
else
{
lean_dec_ref(v_k_1588_);
lean_dec_ref(v_f_1499_);
return v___x_1589_;
}
}
default: 
{
lean_object* v_decl_1591_; lean_object* v_k_1592_; lean_object* v_params_1593_; lean_object* v_type_1594_; lean_object* v_value_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_decl_1591_ = lean_ctor_get(v_c_1500_, 0);
lean_inc_ref(v_decl_1591_);
v_k_1592_ = lean_ctor_get(v_c_1500_, 1);
lean_inc_ref(v_k_1592_);
lean_dec_ref(v_c_1500_);
v_params_1593_ = lean_ctor_get(v_decl_1591_, 2);
lean_inc_ref(v_params_1593_);
v_type_1594_ = lean_ctor_get(v_decl_1591_, 3);
lean_inc_ref(v_type_1594_);
v_value_1595_ = lean_ctor_get(v_decl_1591_, 4);
lean_inc_ref(v_value_1595_);
lean_dec_ref(v_decl_1591_);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_array_get_size(v_params_1593_);
v___x_1598_ = lean_nat_dec_lt(v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref(v_params_1593_);
lean_inc_ref(v_f_1499_);
v___x_1599_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1499_, v_type_1594_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref_known(v___x_1599_, 1);
lean_inc_ref(v_f_1499_);
v___x_1600_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1498_, v_f_1499_, v_value_1595_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_dec_ref_known(v___x_1600_, 1);
v_c_1500_ = v_k_1592_;
goto _start;
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1499_);
return v___x_1600_;
}
}
else
{
lean_dec_ref(v_value_1595_);
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1499_);
return v___x_1599_;
}
}
else
{
lean_object* v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = lean_usize_of_nat(v___x_1597_);
lean_inc_ref(v_f_1499_);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1498_, v_f_1499_, v_params_1593_, v___x_1603_, v___x_1604_, v___x_1602_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec_ref(v_params_1593_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref_known(v___x_1605_, 1);
lean_inc_ref(v_f_1499_);
v___x_1606_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1499_, v_type_1594_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
lean_dec_ref_known(v___x_1606_, 1);
lean_inc_ref(v_f_1499_);
v___x_1607_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1498_, v_f_1499_, v_value_1595_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref_known(v___x_1607_, 1);
v_c_1500_ = v_k_1592_;
goto _start;
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1499_);
return v___x_1607_;
}
}
else
{
lean_dec_ref(v_value_1595_);
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1499_);
return v___x_1606_;
}
}
else
{
lean_dec_ref(v_value_1595_);
lean_dec_ref(v_type_1594_);
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1499_);
return v___x_1605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1609_, lean_object* v_f_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1609_, v_f_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1620_, lean_object* v_f_1621_, lean_object* v_as_1622_, lean_object* v_i_1623_, lean_object* v_stop_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v_pu_boxed_1633_; size_t v_i_boxed_1634_; size_t v_stop_boxed_1635_; lean_object* v_res_1636_; 
v_pu_boxed_1633_ = lean_unbox(v_pu_1620_);
v_i_boxed_1634_ = lean_unbox_usize(v_i_1623_);
lean_dec(v_i_1623_);
v_stop_boxed_1635_ = lean_unbox_usize(v_stop_1624_);
lean_dec(v_stop_1624_);
v_res_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1633_, v_f_1621_, v_as_1622_, v_i_boxed_1634_, v_stop_boxed_1635_, v_b_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v_as_1622_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1637_, lean_object* v_f_1638_, lean_object* v_c_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v_pu_boxed_1647_; lean_object* v_res_1648_; 
v_pu_boxed_1647_ = lean_unbox(v_pu_1637_);
v_res_1648_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1647_, v_f_1638_, v_c_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec(v___y_1640_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1649_, lean_object* v_as_1650_, size_t v_i_1651_, size_t v_stop_1652_, lean_object* v_b_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_eq(v_i_1651_, v_stop_1652_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_inc(v___x_1649_);
v___x_1662_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1662_, 0, v___x_1649_);
v___x_1663_ = lean_array_uget_borrowed(v_as_1650_, v_i_1651_);
lean_inc(v___x_1663_);
v___x_1664_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1662_, v___x_1663_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; size_t v___x_1666_; size_t v___x_1667_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = ((size_t)1ULL);
v___x_1667_ = lean_usize_add(v_i_1651_, v___x_1666_);
v_i_1651_ = v___x_1667_;
v_b_1653_ = v_a_1665_;
goto _start;
}
else
{
lean_dec(v___x_1649_);
return v___x_1664_;
}
}
else
{
lean_object* v___x_1669_; 
lean_dec(v___x_1649_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1653_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1670_, lean_object* v_as_1671_, lean_object* v_i_1672_, lean_object* v_stop_1673_, lean_object* v_b_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
size_t v_i_boxed_1682_; size_t v_stop_boxed_1683_; lean_object* v_res_1684_; 
v_i_boxed_1682_ = lean_unbox_usize(v_i_1672_);
lean_dec(v_i_1672_);
v_stop_boxed_1683_ = lean_unbox_usize(v_stop_1673_);
lean_dec(v_stop_1673_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1670_, v_as_1671_, v_i_boxed_1682_, v_stop_boxed_1683_, v_b_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v_as_1671_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = 0;
v___x_1694_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1685_);
lean_inc(v___x_1694_);
v___x_1695_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1695_, 0, v___x_1694_);
switch(lean_obj_tag(v_alt_1685_))
{
case 0:
{
lean_object* v_params_1696_; lean_object* v_code_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_params_1696_ = lean_ctor_get(v_alt_1685_, 1);
lean_inc_ref(v_params_1696_);
v_code_1697_ = lean_ctor_get(v_alt_1685_, 2);
lean_inc_ref(v_code_1697_);
lean_dec_ref_known(v_alt_1685_, 3);
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = lean_array_get_size(v_params_1696_);
v___x_1700_ = lean_nat_dec_lt(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_dec_ref(v_params_1696_);
lean_dec(v___x_1694_);
v___x_1701_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1693_, v___x_1695_, v_code_1697_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1699_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1694_, v_params_1696_, v___x_1703_, v___x_1704_, v___x_1702_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec_ref(v_params_1696_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1693_, v___x_1695_, v_code_1697_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
return v___x_1706_;
}
else
{
lean_dec_ref(v_code_1697_);
lean_dec_ref(v___x_1695_);
return v___x_1705_;
}
}
}
case 1:
{
lean_object* v_code_1707_; lean_object* v___x_1708_; 
lean_dec(v___x_1694_);
v_code_1707_ = lean_ctor_get(v_alt_1685_, 1);
lean_inc_ref(v_code_1707_);
lean_dec_ref_known(v_alt_1685_, 2);
v___x_1708_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1693_, v___x_1695_, v_code_1707_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
return v___x_1708_;
}
default: 
{
lean_object* v_code_1709_; lean_object* v___x_1710_; 
lean_dec(v___x_1694_);
v_code_1709_ = lean_ctor_get(v_alt_1685_, 0);
lean_inc_ref(v_code_1709_);
lean_dec_ref_known(v_alt_1685_, 1);
v___x_1710_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1693_, v___x_1695_, v_code_1709_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec(v_a_1712_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1720_, lean_object* v_f_1721_, lean_object* v_param_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1721_, v_param_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1731_, lean_object* v_f_1732_, lean_object* v_param_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v_pu_boxed_1741_; lean_object* v_res_1742_; 
v_pu_boxed_1741_ = lean_unbox(v_pu_1731_);
v_res_1742_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1741_, v_f_1732_, v_param_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v___y_1734_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1743_, lean_object* v_alt_1744_, lean_object* v_f_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1744_, v_f_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1754_, lean_object* v_alt_1755_, lean_object* v_f_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v_pu_boxed_1764_; lean_object* v_res_1765_; 
v_pu_boxed_1764_ = lean_unbox(v_pu_1754_);
v_res_1765_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1764_, v_alt_1755_, v_f_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec(v___y_1757_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1766_, lean_object* v_f_1767_, lean_object* v_arg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1767_, v_arg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1777_, lean_object* v_f_1778_, lean_object* v_arg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
uint8_t v_pu_boxed_1787_; lean_object* v_res_1788_; 
v_pu_boxed_1787_ = lean_unbox(v_pu_1777_);
v_res_1788_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1787_, v_f_1778_, v_arg_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1789_, size_t v_i_1790_, size_t v_stop_1791_, lean_object* v_b_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_usize_dec_eq(v_i_1790_, v_stop_1791_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_array_uget_borrowed(v_as_1789_, v_i_1790_);
lean_inc(v___x_1801_);
v___x_1802_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1801_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; size_t v___x_1804_; size_t v___x_1805_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1790_, v___x_1804_);
v_i_1790_ = v___x_1805_;
v_b_1792_ = v_a_1803_;
goto _start;
}
else
{
return v___x_1802_;
}
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_b_1792_);
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1808_, lean_object* v_i_1809_, lean_object* v_stop_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
size_t v_i_boxed_1819_; size_t v_stop_boxed_1820_; lean_object* v_res_1821_; 
v_i_boxed_1819_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_stop_boxed_1820_ = lean_unbox_usize(v_stop_1810_);
lean_dec(v_stop_1810_);
v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1808_, v_i_boxed_1819_, v_stop_boxed_1820_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v_as_1808_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_alts_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_alts_1830_ = lean_ctor_get(v_cs_1822_, 3);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_array_get_size(v_alts_1830_);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_nat_dec_lt(v___x_1831_, v___x_1832_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
return v___x_1835_;
}
else
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_nat_dec_le(v___x_1832_, v___x_1832_);
if (v___x_1836_ == 0)
{
if (v___x_1834_ == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1833_);
return v___x_1837_;
}
else
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((size_t)0ULL);
v___x_1839_ = lean_usize_of_nat(v___x_1832_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1830_, v___x_1838_, v___x_1839_, v___x_1833_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1840_;
}
}
else
{
size_t v___x_1841_; size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((size_t)0ULL);
v___x_1842_ = lean_usize_of_nat(v___x_1832_);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1830_, v___x_1841_, v___x_1842_, v___x_1833_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_cs_1844_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(lean_object* v_as_x27_1853_, lean_object* v_b_1854_){
_start:
{
if (lean_obj_tag(v_as_x27_1853_) == 0)
{
return v_b_1854_;
}
else
{
lean_object* v_head_1855_; lean_object* v_tail_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v_r_1859_; 
v_head_1855_ = lean_ctor_get(v_as_x27_1853_, 0);
v_tail_1856_ = lean_ctor_get(v_as_x27_1853_, 1);
v_fst_1857_ = lean_ctor_get(v_head_1855_, 0);
v_snd_1858_ = lean_ctor_get(v_head_1855_, 1);
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
v_r_1859_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_b_1854_, v_fst_1857_, v_snd_1858_);
v_as_x27_1853_ = v_tail_1856_;
v_b_1854_ = v_r_1859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg___boxed(lean_object* v_as_x27_1861_, lean_object* v_b_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_as_x27_1861_, v_b_1862_);
lean_dec(v_as_x27_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(lean_object* v_m_1864_, lean_object* v_l_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_l_1865_, v_m_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___boxed(lean_object* v_m_1867_, lean_object* v_l_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(v_m_1867_, v_l_1868_);
lean_dec(v_l_1868_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
if (lean_obj_tag(v_a_1870_) == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = l_List_reverse___redArg(v_a_1871_);
return v___x_1872_;
}
else
{
lean_object* v_head_1873_; lean_object* v_tail_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1885_; 
v_head_1873_ = lean_ctor_get(v_a_1870_, 0);
v_tail_1874_ = lean_ctor_get(v_a_1870_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_a_1870_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1876_ = v_a_1870_;
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_tail_1874_);
lean_inc(v_head_1873_);
lean_dec(v_a_1870_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1878_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1873_);
lean_dec(v_head_1873_);
v___x_1879_ = lean_box(2);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_a_1871_);
lean_ctor_set(v___x_1876_, 0, v___x_1880_);
v___x_1882_ = v___x_1876_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_a_1871_);
v___x_1882_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v_a_1870_ = v_tail_1874_;
v_a_1871_ = v___x_1882_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_x_1886_);
return v___x_1893_;
}
else
{
lean_object* v_head_1894_; lean_object* v_tail_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1957_; 
v_head_1894_ = lean_ctor_get(v_x_1887_, 0);
v_tail_1895_ = lean_ctor_get(v_x_1887_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1897_ = v_x_1887_;
v_isShared_1898_ = v_isSharedCheck_1957_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_tail_1895_);
lean_inc(v_head_1894_);
lean_dec(v_x_1887_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1957_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_fst_1899_; lean_object* v_snd_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1956_; 
v_fst_1899_ = lean_ctor_get(v_x_1886_, 0);
v_snd_1900_ = lean_ctor_get(v_x_1886_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1902_ = v_x_1886_;
v_isShared_1903_ = v_isSharedCheck_1956_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snd_1900_);
lean_inc(v_fst_1899_);
lean_dec(v_x_1886_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1956_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; 
if (lean_obj_tag(v_head_1894_) == 0)
{
lean_object* v_decl_1937_; lean_object* v___x_1938_; 
v_decl_1937_ = lean_ctor_get(v_head_1894_, 0);
lean_inc_ref(v_decl_1937_);
v___x_1938_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_1937_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
if (v___x_1940_ == 0)
{
lean_del_object(v___x_1897_);
v___y_1905_ = v___y_1888_;
v___y_1906_ = v___y_1889_;
v___y_1907_ = v___y_1890_;
v___y_1908_ = v___y_1891_;
goto v___jp_1904_;
}
else
{
lean_object* v_fvarId_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_inc_ref(v_decl_1937_);
lean_dec_ref_known(v_head_1894_, 1);
lean_del_object(v___x_1902_);
v_fvarId_1941_ = lean_ctor_get(v_decl_1937_, 0);
lean_inc(v_fvarId_1941_);
lean_dec_ref(v_decl_1937_);
v___x_1942_ = lean_box(2);
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1899_, v_fvarId_1941_, v___x_1942_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 0);
lean_ctor_set(v___x_1897_, 1, v_snd_1900_);
lean_ctor_set(v___x_1897_, 0, v___x_1943_);
v___x_1945_ = v___x_1897_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_snd_1900_);
v___x_1945_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
v_x_1886_ = v___x_1945_;
v_x_1887_ = v_tail_1895_;
goto _start;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref_known(v_head_1894_, 1);
lean_del_object(v___x_1902_);
lean_dec(v_snd_1900_);
lean_dec(v_fst_1899_);
lean_del_object(v___x_1897_);
lean_dec(v_tail_1895_);
v_a_1948_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1938_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1938_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_del_object(v___x_1897_);
v___y_1905_ = v___y_1888_;
v___y_1906_ = v___y_1889_;
v___y_1907_ = v___y_1890_;
v___y_1908_ = v___y_1891_;
goto v___jp_1904_;
}
v___jp_1904_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_st_ref_get(v___y_1908_);
lean_dec(v___x_1909_);
v___x_1910_ = lean_st_mk_ref(v_snd_1900_);
lean_inc(v_head_1894_);
v___x_1911_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1894_, v___x_1910_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = lean_st_ref_get(v___x_1910_);
lean_dec(v___x_1910_);
v___x_1914_ = lean_unbox(v_a_1912_);
lean_dec(v_a_1912_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1915_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1894_);
lean_dec(v_head_1894_);
v___x_1916_ = lean_box(3);
v___x_1917_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1899_, v___x_1915_, v___x_1916_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v___x_1913_);
lean_ctor_set(v___x_1902_, 0, v___x_1917_);
v___x_1919_ = v___x_1902_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1913_);
v___x_1919_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
v_x_1886_ = v___x_1919_;
v_x_1887_ = v_tail_1895_;
goto _start;
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1922_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1894_);
lean_dec(v_head_1894_);
v___x_1923_ = lean_box(2);
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1899_, v___x_1922_, v___x_1923_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v___x_1913_);
lean_ctor_set(v___x_1902_, 0, v___x_1924_);
v___x_1926_ = v___x_1902_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1913_);
v___x_1926_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
v_x_1886_ = v___x_1926_;
v_x_1887_ = v_tail_1895_;
goto _start;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v___x_1910_);
lean_del_object(v___x_1902_);
lean_dec(v_fst_1899_);
lean_dec(v_tail_1895_);
lean_dec(v_head_1894_);
v_a_1929_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1911_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1911_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_1958_, v_x_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1965_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_unsigned_to_nat(16u);
v___x_1968_ = lean_mk_array(v___x_1967_, v___x_1966_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_map_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v_typeName_2014_; lean_object* v_discr_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___y_2028_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_typeName_2014_ = lean_ctor_get(v_cs_1981_, 0);
v_discr_2015_ = lean_ctor_get(v_cs_1981_, 2);
v___x_2016_ = l_List_lengthTR___redArg(v_a_1982_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_unsigned_to_nat(4u);
v___x_2019_ = lean_nat_mul(v___x_2016_, v___x_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_unsigned_to_nat(3u);
v___x_2021_ = lean_nat_div(v___x_2019_, v___x_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = l_Nat_nextPowerOfTwo(v___x_2021_);
lean_dec(v___x_2021_);
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_mk_array(v___x_2022_, v___x_2023_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2017_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2048_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4));
v___x_2049_ = lean_name_eq(v_typeName_2014_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6));
v___x_2051_ = lean_name_eq(v_typeName_2014_, v___x_2050_);
v___y_2028_ = v___x_2051_;
goto v___jp_2027_;
}
else
{
v___y_2028_ = v___x_2049_;
goto v___jp_2027_;
}
v___jp_1988_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_st_mk_ref(v_map_1989_);
v___x_1996_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1981_, v___x_1995_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec_ref(v_cs_1981_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1996_, 0);
lean_dec(v_unused_2005_);
v___x_1998_ = v___x_1996_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v___x_1996_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_st_ref_get(v___x_1995_);
lean_dec(v___x_1995_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v___x_1995_);
v_a_2006_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1996_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1996_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
v___jp_2027_:
{
if (v___y_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2025_);
lean_ctor_set(v___x_2029_, 1, v___x_2026_);
lean_inc(v_a_1982_);
v___x_2030_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2029_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v_fst_2032_; uint8_t v___x_2033_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v_fst_2032_ = lean_ctor_get(v_a_2031_, 0);
lean_inc(v_fst_2032_);
lean_dec(v_a_2031_);
v___x_2033_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2032_, v_discr_2015_);
if (v___x_2033_ == 0)
{
v_map_1989_ = v_fst_2032_;
v___y_1990_ = v_a_1982_;
v___y_1991_ = v_a_1983_;
v___y_1992_ = v_a_1984_;
v___y_1993_ = v_a_1985_;
v___y_1994_ = v_a_1986_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_box(2);
lean_inc(v_discr_2015_);
v___x_2035_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2032_, v_discr_2015_, v___x_2034_);
v_map_1989_ = v___x_2035_;
v___y_1990_ = v_a_1982_;
v___y_1991_ = v_a_1983_;
v___y_1992_ = v_a_1984_;
v___y_1993_ = v_a_1985_;
v___y_1994_ = v_a_1986_;
goto v___jp_1988_;
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_cs_1981_);
v_a_2036_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2030_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2030_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec_ref_known(v___x_2025_, 2);
lean_dec_ref(v_cs_1981_);
v___x_2044_ = lean_box(0);
lean_inc(v_a_1982_);
v___x_2045_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(v_a_1982_, v___x_2044_);
v___x_2046_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v___x_2045_, v___x_2026_);
lean_dec(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2060_, v_x_2061_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2069_, v_x_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(lean_object* v_as_2078_, lean_object* v_as_x27_2079_, lean_object* v_b_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_as_x27_2079_, v_b_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___boxed(lean_object* v_as_2083_, lean_object* v_as_x27_2084_, lean_object* v_b_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(v_as_2083_, v_as_x27_2084_, v_b_2085_, v_a_2086_);
lean_dec(v_as_x27_2084_);
lean_dec(v_as_2083_);
return v_res_2087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
return v___x_2090_;
}
else
{
lean_object* v_key_2091_; lean_object* v_tail_2092_; uint8_t v___x_2093_; 
v_key_2091_ = lean_ctor_get(v_x_2089_, 0);
v_tail_2092_ = lean_ctor_get(v_x_2089_, 2);
v___x_2093_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2091_, v_a_2088_);
if (v___x_2093_ == 0)
{
v_x_2089_ = v_tail_2092_;
goto _start;
}
else
{
return v___x_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_a_2095_, lean_object* v_x_2096_){
_start:
{
uint8_t v_res_2097_; lean_object* v_r_2098_; 
v_res_2097_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2095_, v_x_2096_);
lean_dec(v_x_2096_);
lean_dec(v_a_2095_);
v_r_2098_ = lean_box(v_res_2097_);
return v_r_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object* v_a_2099_, lean_object* v_b_2100_, lean_object* v_x_2101_){
_start:
{
if (lean_obj_tag(v_x_2101_) == 0)
{
lean_dec(v_b_2100_);
lean_dec(v_a_2099_);
return v_x_2101_;
}
else
{
lean_object* v_key_2102_; lean_object* v_value_2103_; lean_object* v_tail_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2116_; 
v_key_2102_ = lean_ctor_get(v_x_2101_, 0);
v_value_2103_ = lean_ctor_get(v_x_2101_, 1);
v_tail_2104_ = lean_ctor_get(v_x_2101_, 2);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_x_2101_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2106_ = v_x_2101_;
v_isShared_2107_ = v_isSharedCheck_2116_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_tail_2104_);
lean_inc(v_value_2103_);
lean_inc(v_key_2102_);
lean_dec(v_x_2101_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2116_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
uint8_t v___x_2108_; 
v___x_2108_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2102_, v_a_2099_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2099_, v_b_2100_, v_tail_2104_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 2, v___x_2109_);
v___x_2111_ = v___x_2106_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_key_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_value_2103_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
else
{
lean_object* v___x_2114_; 
lean_dec(v_value_2103_);
lean_dec(v_key_2102_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v_b_2100_);
lean_ctor_set(v___x_2106_, 0, v_a_2099_);
v___x_2114_ = v___x_2106_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2099_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_b_2100_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_tail_2104_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
return v_x_2117_;
}
else
{
lean_object* v_key_2119_; lean_object* v_value_2120_; lean_object* v_tail_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2144_; 
v_key_2119_ = lean_ctor_get(v_x_2118_, 0);
v_value_2120_ = lean_ctor_get(v_x_2118_, 1);
v_tail_2121_ = lean_ctor_get(v_x_2118_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2123_ = v_x_2118_;
v_isShared_2124_ = v_isSharedCheck_2144_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_tail_2121_);
lean_inc(v_value_2120_);
lean_inc(v_key_2119_);
lean_dec(v_x_2118_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2144_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint64_t v_fold_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2125_ = lean_array_get_size(v_x_2117_);
v___x_2126_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_2119_);
v___x_2127_ = 32ULL;
v___x_2128_ = lean_uint64_shift_right(v___x_2126_, v___x_2127_);
v_fold_2129_ = lean_uint64_xor(v___x_2126_, v___x_2128_);
v___x_2130_ = 16ULL;
v___x_2131_ = lean_uint64_shift_right(v_fold_2129_, v___x_2130_);
v___x_2132_ = lean_uint64_xor(v_fold_2129_, v___x_2131_);
v___x_2133_ = lean_uint64_to_usize(v___x_2132_);
v___x_2134_ = lean_usize_of_nat(v___x_2125_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_sub(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_usize_land(v___x_2133_, v___x_2136_);
v___x_2138_ = lean_array_uget_borrowed(v_x_2117_, v___x_2137_);
lean_inc(v___x_2138_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 2, v___x_2138_);
v___x_2140_ = v___x_2123_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_key_2119_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_value_2120_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_array_uset(v_x_2117_, v___x_2137_, v___x_2140_);
v_x_2117_ = v___x_2141_;
v_x_2118_ = v_tail_2121_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2145_, lean_object* v_source_2146_, lean_object* v_target_2147_){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_array_get_size(v_source_2146_);
v___x_2149_ = lean_nat_dec_lt(v_i_2145_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_dec_ref(v_source_2146_);
lean_dec(v_i_2145_);
return v_target_2147_;
}
else
{
lean_object* v_es_2150_; lean_object* v___x_2151_; lean_object* v_source_2152_; lean_object* v_target_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_es_2150_ = lean_array_fget(v_source_2146_, v_i_2145_);
v___x_2151_ = lean_box(0);
v_source_2152_ = lean_array_fset(v_source_2146_, v_i_2145_, v___x_2151_);
v_target_2153_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2147_, v_es_2150_);
v___x_2154_ = lean_unsigned_to_nat(1u);
v___x_2155_ = lean_nat_add(v_i_2145_, v___x_2154_);
lean_dec(v_i_2145_);
v_i_2145_ = v___x_2155_;
v_source_2146_ = v_source_2152_;
v_target_2147_ = v_target_2153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object* v_data_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v_nbuckets_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2158_ = lean_array_get_size(v_data_2157_);
v___x_2159_ = lean_unsigned_to_nat(2u);
v_nbuckets_2160_ = lean_nat_mul(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_mk_array(v_nbuckets_2160_, v___x_2162_);
v___x_2164_ = lean_array_propagate_mark(v_data_2157_, v___x_2163_);
v___x_2165_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2161_, v_data_2157_, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2166_, lean_object* v_a_2167_, lean_object* v_b_2168_){
_start:
{
lean_object* v_size_2169_; lean_object* v_buckets_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2213_; 
v_size_2169_ = lean_ctor_get(v_m_2166_, 0);
v_buckets_2170_ = lean_ctor_get(v_m_2166_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_m_2166_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2172_ = v_m_2166_;
v_isShared_2173_ = v_isSharedCheck_2213_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_buckets_2170_);
lean_inc(v_size_2169_);
lean_dec(v_m_2166_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2213_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; uint64_t v___x_2177_; uint64_t v_fold_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v_bkt_2187_; uint8_t v___x_2188_; 
v___x_2174_ = lean_array_get_size(v_buckets_2170_);
v___x_2175_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2167_);
v___x_2176_ = 32ULL;
v___x_2177_ = lean_uint64_shift_right(v___x_2175_, v___x_2176_);
v_fold_2178_ = lean_uint64_xor(v___x_2175_, v___x_2177_);
v___x_2179_ = 16ULL;
v___x_2180_ = lean_uint64_shift_right(v_fold_2178_, v___x_2179_);
v___x_2181_ = lean_uint64_xor(v_fold_2178_, v___x_2180_);
v___x_2182_ = lean_uint64_to_usize(v___x_2181_);
v___x_2183_ = lean_usize_of_nat(v___x_2174_);
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_sub(v___x_2183_, v___x_2184_);
v___x_2186_ = lean_usize_land(v___x_2182_, v___x_2185_);
v_bkt_2187_ = lean_array_uget_borrowed(v_buckets_2170_, v___x_2186_);
v___x_2188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2167_, v_bkt_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v_size_x27_2190_; lean_object* v___x_2191_; lean_object* v_buckets_x27_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2189_ = lean_unsigned_to_nat(1u);
v_size_x27_2190_ = lean_nat_add(v_size_2169_, v___x_2189_);
lean_dec(v_size_2169_);
lean_inc(v_bkt_2187_);
v___x_2191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2167_);
lean_ctor_set(v___x_2191_, 1, v_b_2168_);
lean_ctor_set(v___x_2191_, 2, v_bkt_2187_);
v_buckets_x27_2192_ = lean_array_uset(v_buckets_2170_, v___x_2186_, v___x_2191_);
v___x_2193_ = lean_unsigned_to_nat(4u);
v___x_2194_ = lean_nat_mul(v_size_x27_2190_, v___x_2193_);
v___x_2195_ = lean_unsigned_to_nat(3u);
v___x_2196_ = lean_nat_div(v___x_2194_, v___x_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_array_get_size(v_buckets_x27_2192_);
v___x_2198_ = lean_nat_dec_le(v___x_2196_, v___x_2197_);
lean_dec(v___x_2196_);
if (v___x_2198_ == 0)
{
lean_object* v_val_2199_; lean_object* v___x_2201_; 
v_val_2199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2192_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v_val_2199_);
lean_ctor_set(v___x_2172_, 0, v_size_x27_2190_);
v___x_2201_ = v___x_2172_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_size_x27_2190_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_val_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
else
{
lean_object* v___x_2204_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v_buckets_x27_2192_);
lean_ctor_set(v___x_2172_, 0, v_size_x27_2190_);
v___x_2204_ = v___x_2172_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_size_x27_2190_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_buckets_x27_2192_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v_buckets_x27_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_inc(v_bkt_2187_);
v___x_2206_ = lean_box(0);
v_buckets_x27_2207_ = lean_array_uset(v_buckets_2170_, v___x_2186_, v___x_2206_);
v___x_2208_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2167_, v_b_2168_, v_bkt_2187_);
v___x_2209_ = lean_array_uset(v_buckets_x27_2207_, v___x_2186_, v___x_2208_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2209_);
v___x_2211_ = v___x_2172_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_size_2169_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2214_, size_t v_i_2215_, size_t v_stop_2216_, lean_object* v_b_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_usize_dec_eq(v_i_2215_, v_stop_2216_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = ((size_t)1ULL);
v___x_2221_ = lean_usize_sub(v_i_2215_, v___x_2220_);
v___x_2222_ = lean_array_uget_borrowed(v_as_2214_, v___x_2221_);
v___x_2223_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2222_);
v___x_2224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2217_, v___x_2223_, v___x_2219_);
v_i_2215_ = v___x_2221_;
v_b_2217_ = v___x_2224_;
goto _start;
}
else
{
return v_b_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2226_, lean_object* v_i_2227_, lean_object* v_stop_2228_, lean_object* v_b_2229_){
_start:
{
size_t v_i_boxed_2230_; size_t v_stop_boxed_2231_; lean_object* v_res_2232_; 
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_stop_boxed_2231_ = lean_unbox_usize(v_stop_2228_);
lean_dec(v_stop_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2226_, v_i_boxed_2230_, v_stop_boxed_2231_, v_b_2229_);
lean_dec_ref(v_as_2226_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2233_){
_start:
{
lean_object* v_alts_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_map_2249_; uint8_t v___x_2250_; 
v_alts_2234_ = lean_ctor_get(v_cs_2233_, 3);
v___x_2235_ = lean_array_get_size(v_alts_2234_);
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_add(v___x_2235_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_unsigned_to_nat(4u);
v___x_2240_ = lean_nat_mul(v___x_2237_, v___x_2239_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_unsigned_to_nat(3u);
v___x_2242_ = lean_nat_div(v___x_2240_, v___x_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = l_Nat_nextPowerOfTwo(v___x_2242_);
lean_dec(v___x_2242_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_mk_array(v___x_2243_, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2238_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_box(2);
v___x_2248_ = lean_box(0);
v_map_2249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2246_, v___x_2247_, v___x_2248_);
v___x_2250_ = lean_nat_dec_lt(v___x_2238_, v___x_2235_);
if (v___x_2250_ == 0)
{
return v_map_2249_;
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_usize_of_nat(v___x_2235_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2234_, v___x_2251_, v___x_2252_, v_map_2249_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2254_);
lean_dec_ref(v_cs_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2256_, lean_object* v_m_2257_, lean_object* v_a_2258_, lean_object* v_b_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2257_, v_a_2258_, v_b_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2261_, lean_object* v_a_2262_, lean_object* v_x_2263_){
_start:
{
uint8_t v___x_2264_; 
v___x_2264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2262_, v_x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2265_, lean_object* v_a_2266_, lean_object* v_x_2267_){
_start:
{
uint8_t v_res_2268_; lean_object* v_r_2269_; 
v_res_2268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2265_, v_a_2266_, v_x_2267_);
lean_dec(v_x_2267_);
lean_dec(v_a_2266_);
v_r_2269_ = lean_box(v_res_2268_);
return v_r_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2270_, lean_object* v_data_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2273_, lean_object* v_a_2274_, lean_object* v_b_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2274_, v_b_2275_, v_x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2278_, lean_object* v_i_2279_, lean_object* v_source_2280_, lean_object* v_target_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2279_, v_source_2280_, v_target_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2284_, v_x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; lean_object* v_decision_2291_; uint8_t v___x_2292_; 
v___x_2290_ = lean_st_ref_get(v_a_2288_);
v_decision_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_ref(v_decision_2291_);
lean_dec(v___x_2290_);
v___x_2292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2291_, v_fvar_2287_);
lean_dec_ref(v_decision_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec(v_fvar_2287_);
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
else
{
lean_object* v___x_2295_; lean_object* v_decision_2296_; lean_object* v_newArms_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2309_; 
v___x_2295_ = lean_st_ref_take(v_a_2288_);
v_decision_2296_ = lean_ctor_get(v___x_2295_, 0);
v_newArms_2297_ = lean_ctor_get(v___x_2295_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2299_ = v___x_2295_;
v_isShared_2300_ = v_isSharedCheck_2309_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_newArms_2297_);
lean_inc(v_decision_2296_);
lean_dec(v___x_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2309_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2301_ = lean_box(0);
v___x_2302_ = lean_box(2);
v___x_2303_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2296_, v_fvar_2287_, v___x_2302_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2303_);
v___x_2305_ = v___x_2299_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_newArms_2297_);
v___x_2305_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_st_ref_put(v_a_2288_, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2301_);
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2310_, v_a_2311_);
lean_dec(v_a_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2314_, v_a_2315_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec(v_a_2324_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v_toApplicative_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2405_; 
v___x_2340_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2341_ = l_StateRefT_x27_instMonad___redArg(v___x_2340_);
v_toApplicative_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2341_, 1);
lean_dec(v_unused_2406_);
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2405_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_toApplicative_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2405_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_toFunctor_2346_; lean_object* v_toSeq_2347_; lean_object* v_toSeqLeft_2348_; lean_object* v_toSeqRight_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2403_; 
v_toFunctor_2346_ = lean_ctor_get(v_toApplicative_2342_, 0);
v_toSeq_2347_ = lean_ctor_get(v_toApplicative_2342_, 2);
v_toSeqLeft_2348_ = lean_ctor_get(v_toApplicative_2342_, 3);
v_toSeqRight_2349_ = lean_ctor_get(v_toApplicative_2342_, 4);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_toApplicative_2342_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_toApplicative_2342_, 1);
lean_dec(v_unused_2404_);
v___x_2351_ = v_toApplicative_2342_;
v_isShared_2352_ = v_isSharedCheck_2403_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_toSeqRight_2349_);
lean_inc(v_toSeqLeft_2348_);
lean_inc(v_toSeq_2347_);
lean_inc(v_toFunctor_2346_);
lean_dec(v_toApplicative_2342_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2403_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___f_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___f_2360_; lean_object* v___x_2362_; 
v___f_2353_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2354_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2346_);
v___f_2355_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2355_, 0, v_toFunctor_2346_);
v___f_2356_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2356_, 0, v_toFunctor_2346_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___f_2355_);
lean_ctor_set(v___x_2357_, 1, v___f_2356_);
v___f_2358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2358_, 0, v_toSeqRight_2349_);
v___f_2359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2359_, 0, v_toSeqLeft_2348_);
v___f_2360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2360_, 0, v_toSeq_2347_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 4, v___f_2358_);
lean_ctor_set(v___x_2351_, 3, v___f_2359_);
lean_ctor_set(v___x_2351_, 2, v___f_2360_);
lean_ctor_set(v___x_2351_, 1, v___f_2353_);
lean_ctor_set(v___x_2351_, 0, v___x_2357_);
v___x_2362_ = v___x_2351_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___f_2353_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v___f_2360_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v___f_2359_);
lean_ctor_set(v_reuseFailAlloc_2402_, 4, v___f_2358_);
v___x_2362_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v___f_2354_);
lean_ctor_set(v___x_2344_, 0, v___x_2362_);
v___x_2364_ = v___x_2344_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___f_2354_);
v___x_2364_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v_toApplicative_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2399_; 
v___x_2365_ = l_StateRefT_x27_instMonad___redArg(v___x_2364_);
v_toApplicative_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2365_, 1);
lean_dec(v_unused_2400_);
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2399_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_toApplicative_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2399_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v_toFunctor_2370_; lean_object* v_toSeq_2371_; lean_object* v_toSeqLeft_2372_; lean_object* v_toSeqRight_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2397_; 
v_toFunctor_2370_ = lean_ctor_get(v_toApplicative_2366_, 0);
v_toSeq_2371_ = lean_ctor_get(v_toApplicative_2366_, 2);
v_toSeqLeft_2372_ = lean_ctor_get(v_toApplicative_2366_, 3);
v_toSeqRight_2373_ = lean_ctor_get(v_toApplicative_2366_, 4);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_toApplicative_2366_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v_toApplicative_2366_, 1);
lean_dec(v_unused_2398_);
v___x_2375_ = v_toApplicative_2366_;
v_isShared_2376_ = v_isSharedCheck_2397_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_toSeqRight_2373_);
lean_inc(v_toSeqLeft_2372_);
lean_inc(v_toSeq_2371_);
lean_inc(v_toFunctor_2370_);
lean_dec(v_toApplicative_2366_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2397_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___f_2377_; lean_object* v___f_2378_; lean_object* v___f_2379_; lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___f_2383_; lean_object* v___f_2384_; lean_object* v___x_2386_; 
v___f_2377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2370_);
v___f_2379_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2379_, 0, v_toFunctor_2370_);
v___f_2380_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2380_, 0, v_toFunctor_2370_);
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___f_2379_);
lean_ctor_set(v___x_2381_, 1, v___f_2380_);
v___f_2382_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2382_, 0, v_toSeqRight_2373_);
v___f_2383_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2383_, 0, v_toSeqLeft_2372_);
v___f_2384_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2384_, 0, v_toSeq_2371_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 4, v___f_2382_);
lean_ctor_set(v___x_2375_, 3, v___f_2383_);
lean_ctor_set(v___x_2375_, 2, v___f_2384_);
lean_ctor_set(v___x_2375_, 1, v___f_2377_);
lean_ctor_set(v___x_2375_, 0, v___x_2381_);
v___x_2386_ = v___x_2375_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___f_2377_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v___f_2384_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v___f_2383_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v___f_2382_);
v___x_2386_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v___f_2378_);
lean_ctor_set(v___x_2368_, 0, v___x_2386_);
v___x_2388_ = v___x_2368_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___f_2378_);
v___x_2388_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_10720__overap_2393_; lean_object* v___x_2394_; 
v___x_2389_ = l_ReaderT_instMonad___redArg(v___x_2388_);
v___x_2390_ = l_StateRefT_x27_instMonad___redArg(v___x_2389_);
v___x_2391_ = lean_box(0);
v___x_2392_ = l_instInhabitedOfMonad___redArg(v___x_2390_, v___x_2391_);
v___x_10720__overap_2393_ = lean_panic_fn_borrowed(v___x_2392_, v_msg_2332_);
lean_dec(v___x_2392_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc(v___y_2336_);
lean_inc_ref(v___y_2335_);
lean_inc(v___y_2334_);
lean_inc(v___y_2333_);
v___x_2394_ = lean_apply_7(v___x_10720__overap_2393_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, lean_box(0));
return v___x_2394_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2416_, lean_object* v_e_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_ty_2426_; lean_object* v_body_2427_; uint8_t v___x_2430_; 
v___x_2430_ = l_Lean_Expr_hasFVar(v_e_2417_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_dec_ref(v_e_2417_);
lean_dec_ref(v_f_2416_);
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
else
{
switch(lean_obj_tag(v_e_2417_))
{
case 1:
{
lean_object* v_fvarId_2433_; lean_object* v___x_2434_; 
v_fvarId_2433_ = lean_ctor_get(v_e_2417_, 0);
lean_inc(v_fvarId_2433_);
lean_dec_ref_known(v_e_2417_, 1);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc(v___y_2418_);
v___x_2434_ = lean_apply_8(v_f_2416_, v_fvarId_2433_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, lean_box(0));
return v___x_2434_;
}
case 2:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref_known(v_e_2417_, 1);
lean_dec_ref(v_f_2416_);
v___x_2435_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2436_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2435_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2436_;
}
case 5:
{
lean_object* v_fn_2437_; lean_object* v_arg_2438_; lean_object* v___x_2439_; 
v_fn_2437_ = lean_ctor_get(v_e_2417_, 0);
lean_inc_ref(v_fn_2437_);
v_arg_2438_ = lean_ctor_get(v_e_2417_, 1);
lean_inc_ref(v_arg_2438_);
lean_dec_ref_known(v_e_2417_, 2);
lean_inc_ref(v_f_2416_);
v___x_2439_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2416_, v_fn_2437_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_dec_ref_known(v___x_2439_, 1);
v_e_2417_ = v_arg_2438_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2438_);
lean_dec_ref(v_f_2416_);
return v___x_2439_;
}
}
case 6:
{
lean_object* v_binderType_2441_; lean_object* v_body_2442_; 
v_binderType_2441_ = lean_ctor_get(v_e_2417_, 1);
lean_inc_ref(v_binderType_2441_);
v_body_2442_ = lean_ctor_get(v_e_2417_, 2);
lean_inc_ref(v_body_2442_);
lean_dec_ref_known(v_e_2417_, 3);
v_ty_2426_ = v_binderType_2441_;
v_body_2427_ = v_body_2442_;
goto v___jp_2425_;
}
case 7:
{
lean_object* v_binderType_2443_; lean_object* v_body_2444_; 
v_binderType_2443_ = lean_ctor_get(v_e_2417_, 1);
lean_inc_ref(v_binderType_2443_);
v_body_2444_ = lean_ctor_get(v_e_2417_, 2);
lean_inc_ref(v_body_2444_);
lean_dec_ref_known(v_e_2417_, 3);
v_ty_2426_ = v_binderType_2443_;
v_body_2427_ = v_body_2444_;
goto v___jp_2425_;
}
case 8:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec_ref_known(v_e_2417_, 4);
lean_dec_ref(v_f_2416_);
v___x_2445_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2446_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2445_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2446_;
}
case 11:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref_known(v_e_2417_, 3);
lean_dec_ref(v_f_2416_);
v___x_2447_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2448_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2447_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2448_;
}
default: 
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_e_2417_);
lean_dec_ref(v_f_2416_);
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
}
v___jp_2425_:
{
lean_object* v___x_2428_; 
lean_inc_ref(v_f_2416_);
v___x_2428_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2416_, v_ty_2426_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_dec_ref_known(v___x_2428_, 1);
v_e_2417_ = v_body_2427_;
goto _start;
}
else
{
lean_dec_ref(v_body_2427_);
lean_dec_ref(v_f_2416_);
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2451_, lean_object* v_e_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2451_, v_e_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec(v___y_2453_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2461_, lean_object* v_arg_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
switch(lean_obj_tag(v_arg_2462_))
{
case 0:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec_ref(v_f_2461_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
case 1:
{
lean_object* v_fvarId_2472_; lean_object* v___x_2473_; 
v_fvarId_2472_ = lean_ctor_get(v_arg_2462_, 0);
lean_inc(v_fvarId_2472_);
lean_dec_ref_known(v_arg_2462_, 1);
lean_inc(v___y_2468_);
lean_inc_ref(v___y_2467_);
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2465_);
lean_inc(v___y_2464_);
lean_inc(v___y_2463_);
v___x_2473_ = lean_apply_8(v_f_2461_, v_fvarId_2472_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, lean_box(0));
return v___x_2473_;
}
default: 
{
lean_object* v_expr_2474_; lean_object* v___x_2475_; 
v_expr_2474_ = lean_ctor_get(v_arg_2462_, 0);
lean_inc_ref(v_expr_2474_);
lean_dec_ref_known(v_arg_2462_, 1);
v___x_2475_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2461_, v_expr_2474_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2476_, lean_object* v_arg_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2476_, v_arg_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2486_, lean_object* v_param_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_type_2495_; lean_object* v___x_2496_; 
v_type_2495_ = lean_ctor_get(v_param_2487_, 2);
lean_inc_ref(v_type_2495_);
lean_dec_ref(v_param_2487_);
v___x_2496_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2486_, v_type_2495_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2497_, lean_object* v_param_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2497_, v_param_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2507_, lean_object* v_f_2508_, lean_object* v_as_2509_, size_t v_i_2510_, size_t v_stop_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_eq(v_i_2510_, v_stop_2511_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_array_uget_borrowed(v_as_2509_, v_i_2510_);
lean_inc(v___x_2521_);
lean_inc_ref(v_f_2508_);
v___x_2522_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2508_, v___x_2521_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; size_t v___x_2524_; size_t v___x_2525_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2510_, v___x_2524_);
v_i_2510_ = v___x_2525_;
v_b_2512_ = v_a_2523_;
goto _start;
}
else
{
lean_dec_ref(v_f_2508_);
return v___x_2522_;
}
}
else
{
lean_object* v___x_2527_; 
lean_dec_ref(v_f_2508_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_b_2512_);
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2528_, lean_object* v_f_2529_, lean_object* v_as_2530_, lean_object* v_i_2531_, lean_object* v_stop_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v_pu_boxed_2541_; size_t v_i_boxed_2542_; size_t v_stop_boxed_2543_; lean_object* v_res_2544_; 
v_pu_boxed_2541_ = lean_unbox(v_pu_2528_);
v_i_boxed_2542_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_stop_boxed_2543_ = lean_unbox_usize(v_stop_2532_);
lean_dec(v_stop_2532_);
v_res_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2541_, v_f_2529_, v_as_2530_, v_i_boxed_2542_, v_stop_boxed_2543_, v_b_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v_as_2530_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2545_, lean_object* v_f_2546_, lean_object* v_as_2547_, size_t v_i_2548_, size_t v_stop_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_usize_dec_eq(v_i_2548_, v_stop_2549_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_array_uget_borrowed(v_as_2547_, v_i_2548_);
lean_inc(v___x_2559_);
lean_inc_ref(v_f_2546_);
v___x_2560_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2546_, v___x_2559_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; size_t v___x_2562_; size_t v___x_2563_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_add(v_i_2548_, v___x_2562_);
v_i_2548_ = v___x_2563_;
v_b_2550_ = v_a_2561_;
goto _start;
}
else
{
lean_dec_ref(v_f_2546_);
return v___x_2560_;
}
}
else
{
lean_object* v___x_2565_; 
lean_dec_ref(v_f_2546_);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_b_2550_);
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2566_, lean_object* v_f_2567_, lean_object* v_as_2568_, lean_object* v_i_2569_, lean_object* v_stop_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v_pu_boxed_2579_; size_t v_i_boxed_2580_; size_t v_stop_boxed_2581_; lean_object* v_res_2582_; 
v_pu_boxed_2579_ = lean_unbox(v_pu_2566_);
v_i_boxed_2580_ = lean_unbox_usize(v_i_2569_);
lean_dec(v_i_2569_);
v_stop_boxed_2581_ = lean_unbox_usize(v_stop_2570_);
lean_dec(v_stop_2570_);
v_res_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2579_, v_f_2567_, v_as_2568_, v_i_boxed_2580_, v_stop_boxed_2581_, v_b_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v_as_2568_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2583_, lean_object* v_f_2584_, lean_object* v_e_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_args_2594_; 
switch(lean_obj_tag(v_e_2585_))
{
case 2:
{
lean_object* v_struct_2603_; lean_object* v___x_2604_; 
v_struct_2603_ = lean_ctor_get(v_e_2585_, 2);
lean_inc(v_struct_2603_);
lean_dec_ref_known(v_e_2585_, 3);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2604_ = lean_apply_8(v_f_2584_, v_struct_2603_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2604_;
}
case 3:
{
lean_object* v_args_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v_args_2605_ = lean_ctor_get(v_e_2585_, 2);
lean_inc_ref(v_args_2605_);
lean_dec_ref_known(v_e_2585_, 3);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_array_get_size(v_args_2605_);
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_nat_dec_lt(v___x_2606_, v___x_2607_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
lean_dec_ref(v_args_2605_);
lean_dec_ref(v_f_2584_);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
return v___x_2610_;
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = lean_usize_of_nat(v___x_2607_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2583_, v_f_2584_, v_args_2605_, v___x_2611_, v___x_2612_, v___x_2608_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v_args_2605_);
return v___x_2613_;
}
}
case 4:
{
lean_object* v_fvarId_2614_; lean_object* v_args_2615_; lean_object* v___x_2616_; 
v_fvarId_2614_ = lean_ctor_get(v_e_2585_, 0);
lean_inc(v_fvarId_2614_);
v_args_2615_ = lean_ctor_get(v_e_2585_, 1);
lean_inc_ref(v_args_2615_);
lean_dec_ref_known(v_e_2585_, 2);
lean_inc_ref(v_f_2584_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2616_ = lean_apply_8(v_f_2584_, v_fvarId_2614_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2630_; 
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2616_, 0);
lean_dec(v_unused_2631_);
v___x_2618_ = v___x_2616_;
v_isShared_2619_ = v_isSharedCheck_2630_;
goto v_resetjp_2617_;
}
else
{
lean_dec(v___x_2616_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2630_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get_size(v_args_2615_);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_nat_dec_lt(v___x_2620_, v___x_2621_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2625_; 
lean_dec_ref(v_args_2615_);
lean_dec_ref(v_f_2584_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2622_);
v___x_2625_ = v___x_2618_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2622_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
else
{
size_t v___x_2627_; size_t v___x_2628_; lean_object* v___x_2629_; 
lean_del_object(v___x_2618_);
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = lean_usize_of_nat(v___x_2621_);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2583_, v_f_2584_, v_args_2615_, v___x_2627_, v___x_2628_, v___x_2622_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v_args_2615_);
return v___x_2629_;
}
}
}
else
{
lean_dec_ref(v_args_2615_);
lean_dec_ref(v_f_2584_);
return v___x_2616_;
}
}
case 5:
{
lean_object* v_args_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_args_2632_ = lean_ctor_get(v_e_2585_, 1);
lean_inc_ref(v_args_2632_);
lean_dec_ref_known(v_e_2585_, 2);
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_array_get_size(v_args_2632_);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_nat_dec_lt(v___x_2633_, v___x_2634_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
lean_dec_ref(v_args_2632_);
lean_dec_ref(v_f_2584_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
return v___x_2637_;
}
else
{
size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = lean_usize_of_nat(v___x_2634_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2583_, v_f_2584_, v_args_2632_, v___x_2638_, v___x_2639_, v___x_2635_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v_args_2632_);
return v___x_2640_;
}
}
case 6:
{
lean_object* v_var_2641_; lean_object* v___x_2642_; 
v_var_2641_ = lean_ctor_get(v_e_2585_, 1);
lean_inc(v_var_2641_);
lean_dec_ref_known(v_e_2585_, 2);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2642_ = lean_apply_8(v_f_2584_, v_var_2641_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2642_;
}
case 7:
{
lean_object* v_var_2643_; lean_object* v___x_2644_; 
v_var_2643_ = lean_ctor_get(v_e_2585_, 1);
lean_inc(v_var_2643_);
lean_dec_ref_known(v_e_2585_, 2);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2644_ = lean_apply_8(v_f_2584_, v_var_2643_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2644_;
}
case 8:
{
lean_object* v_var_2645_; lean_object* v___x_2646_; 
v_var_2645_ = lean_ctor_get(v_e_2585_, 2);
lean_inc(v_var_2645_);
lean_dec_ref_known(v_e_2585_, 3);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2646_ = lean_apply_8(v_f_2584_, v_var_2645_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2646_;
}
case 9:
{
lean_object* v_args_2647_; 
v_args_2647_ = lean_ctor_get(v_e_2585_, 1);
lean_inc_ref(v_args_2647_);
lean_dec_ref_known(v_e_2585_, 2);
v_args_2594_ = v_args_2647_;
goto v___jp_2593_;
}
case 10:
{
lean_object* v_args_2648_; 
v_args_2648_ = lean_ctor_get(v_e_2585_, 1);
lean_inc_ref(v_args_2648_);
lean_dec_ref_known(v_e_2585_, 2);
v_args_2594_ = v_args_2648_;
goto v___jp_2593_;
}
case 11:
{
lean_object* v_var_2649_; lean_object* v___x_2650_; 
v_var_2649_ = lean_ctor_get(v_e_2585_, 1);
lean_inc(v_var_2649_);
lean_dec_ref_known(v_e_2585_, 2);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2650_ = lean_apply_8(v_f_2584_, v_var_2649_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2650_;
}
case 12:
{
lean_object* v_var_2651_; lean_object* v_args_2652_; lean_object* v___x_2653_; 
v_var_2651_ = lean_ctor_get(v_e_2585_, 0);
lean_inc(v_var_2651_);
v_args_2652_ = lean_ctor_get(v_e_2585_, 2);
lean_inc_ref(v_args_2652_);
lean_dec_ref_known(v_e_2585_, 3);
lean_inc_ref(v_f_2584_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2653_ = lean_apply_8(v_f_2584_, v_var_2651_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2667_; 
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2653_, 0);
lean_dec(v_unused_2668_);
v___x_2655_ = v___x_2653_;
v_isShared_2656_ = v_isSharedCheck_2667_;
goto v_resetjp_2654_;
}
else
{
lean_dec(v___x_2653_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2667_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = lean_array_get_size(v_args_2652_);
v___x_2659_ = lean_box(0);
v___x_2660_ = lean_nat_dec_lt(v___x_2657_, v___x_2658_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref(v_args_2652_);
lean_dec_ref(v_f_2584_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2659_);
v___x_2662_ = v___x_2655_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2659_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
size_t v___x_2664_; size_t v___x_2665_; lean_object* v___x_2666_; 
lean_del_object(v___x_2655_);
v___x_2664_ = ((size_t)0ULL);
v___x_2665_ = lean_usize_of_nat(v___x_2658_);
v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2583_, v_f_2584_, v_args_2652_, v___x_2664_, v___x_2665_, v___x_2659_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v_args_2652_);
return v___x_2666_;
}
}
}
else
{
lean_dec_ref(v_args_2652_);
lean_dec_ref(v_f_2584_);
return v___x_2653_;
}
}
case 13:
{
lean_object* v_fvarId_2669_; lean_object* v___x_2670_; 
v_fvarId_2669_ = lean_ctor_get(v_e_2585_, 1);
lean_inc(v_fvarId_2669_);
lean_dec_ref_known(v_e_2585_, 2);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2670_ = lean_apply_8(v_f_2584_, v_fvarId_2669_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2670_;
}
case 14:
{
lean_object* v_fvarId_2671_; lean_object* v___x_2672_; 
v_fvarId_2671_ = lean_ctor_get(v_e_2585_, 0);
lean_inc(v_fvarId_2671_);
lean_dec_ref_known(v_e_2585_, 1);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2672_ = lean_apply_8(v_f_2584_, v_fvarId_2671_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2672_;
}
case 15:
{
lean_object* v_fvarId_2673_; lean_object* v___x_2674_; 
v_fvarId_2673_ = lean_ctor_get(v_e_2585_, 0);
lean_inc(v_fvarId_2673_);
lean_dec_ref_known(v_e_2585_, 1);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
v___x_2674_ = lean_apply_8(v_f_2584_, v_fvarId_2673_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2674_;
}
default: 
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec(v_e_2585_);
lean_dec_ref(v_f_2584_);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
v___jp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = lean_array_get_size(v_args_2594_);
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_nat_dec_lt(v___x_2595_, v___x_2596_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; 
lean_dec_ref(v_args_2594_);
lean_dec_ref(v_f_2584_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
return v___x_2599_;
}
else
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((size_t)0ULL);
v___x_2601_ = lean_usize_of_nat(v___x_2596_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2583_, v_f_2584_, v_args_2594_, v___x_2600_, v___x_2601_, v___x_2597_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v_args_2594_);
return v___x_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2677_, lean_object* v_f_2678_, lean_object* v_e_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v_pu_boxed_2687_; lean_object* v_res_2688_; 
v_pu_boxed_2687_ = lean_unbox(v_pu_2677_);
v_res_2688_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2687_, v_f_2678_, v_e_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2689_, lean_object* v_f_2690_, lean_object* v_decl_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_type_2699_; lean_object* v_value_2700_; lean_object* v___x_2701_; 
v_type_2699_ = lean_ctor_get(v_decl_2691_, 2);
lean_inc_ref(v_type_2699_);
v_value_2700_ = lean_ctor_get(v_decl_2691_, 3);
lean_inc(v_value_2700_);
lean_dec_ref(v_decl_2691_);
lean_inc_ref(v_f_2690_);
v___x_2701_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2690_, v_type_2699_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v___x_2702_; 
lean_dec_ref_known(v___x_2701_, 1);
v___x_2702_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2689_, v_f_2690_, v_value_2700_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2702_;
}
else
{
lean_dec(v_value_2700_);
lean_dec_ref(v_f_2690_);
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2703_, lean_object* v_f_2704_, lean_object* v_decl_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
uint8_t v_pu_boxed_2713_; lean_object* v_res_2714_; 
v_pu_boxed_2713_ = lean_unbox(v_pu_2703_);
v_res_2714_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2713_, v_f_2704_, v_decl_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec(v___y_2706_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2715_, lean_object* v_f_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
switch(lean_obj_tag(v_alt_2715_))
{
case 0:
{
lean_object* v_code_2724_; lean_object* v___x_2725_; 
v_code_2724_ = lean_ctor_get(v_alt_2715_, 2);
lean_inc_ref(v_code_2724_);
lean_dec_ref_known(v_alt_2715_, 3);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc(v___y_2717_);
v___x_2725_ = lean_apply_8(v_f_2716_, v_code_2724_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2725_;
}
case 1:
{
lean_object* v_code_2726_; lean_object* v___x_2727_; 
v_code_2726_ = lean_ctor_get(v_alt_2715_, 1);
lean_inc_ref(v_code_2726_);
lean_dec_ref_known(v_alt_2715_, 2);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc(v___y_2717_);
v___x_2727_ = lean_apply_8(v_f_2716_, v_code_2726_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2727_;
}
default: 
{
lean_object* v_code_2728_; lean_object* v___x_2729_; 
v_code_2728_ = lean_ctor_get(v_alt_2715_, 0);
lean_inc_ref(v_code_2728_);
lean_dec_ref_known(v_alt_2715_, 1);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc(v___y_2717_);
v___x_2729_ = lean_apply_8(v_f_2716_, v_code_2728_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2730_, lean_object* v_f_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2730_, v_f_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2732_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2740_, lean_object* v_f_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v_pu_boxed_2750_; lean_object* v_res_2751_; 
v_pu_boxed_2750_ = lean_unbox(v_pu_2740_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2750_, v_f_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2752_, lean_object* v_f_2753_, lean_object* v_as_2754_, size_t v_i_2755_, size_t v_stop_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_usize_dec_eq(v_i_2755_, v_stop_2756_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___f_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2766_ = lean_box(v_pu_2752_);
lean_inc_ref(v_f_2753_);
v___f_2767_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2767_, 0, v___x_2766_);
lean_closure_set(v___f_2767_, 1, v_f_2753_);
v___x_2768_ = lean_array_uget_borrowed(v_as_2754_, v_i_2755_);
lean_inc(v___x_2768_);
v___x_2769_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2768_, v___f_2767_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; size_t v___x_2771_; size_t v___x_2772_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_add(v_i_2755_, v___x_2771_);
v_i_2755_ = v___x_2772_;
v_b_2757_ = v_a_2770_;
goto _start;
}
else
{
lean_dec_ref(v_f_2753_);
return v___x_2769_;
}
}
else
{
lean_object* v___x_2774_; 
lean_dec_ref(v_f_2753_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v_b_2757_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2775_, lean_object* v_f_2776_, lean_object* v_c_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
switch(lean_obj_tag(v_c_2777_))
{
case 0:
{
lean_object* v_decl_2785_; lean_object* v_k_2786_; lean_object* v___x_2787_; 
v_decl_2785_ = lean_ctor_get(v_c_2777_, 0);
lean_inc_ref(v_decl_2785_);
v_k_2786_ = lean_ctor_get(v_c_2777_, 1);
lean_inc_ref(v_k_2786_);
lean_dec_ref_known(v_c_2777_, 2);
lean_inc_ref(v_f_2776_);
v___x_2787_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2775_, v_f_2776_, v_decl_2785_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_dec_ref_known(v___x_2787_, 1);
v_c_2777_ = v_k_2786_;
goto _start;
}
else
{
lean_dec_ref(v_k_2786_);
lean_dec_ref(v_f_2776_);
return v___x_2787_;
}
}
case 3:
{
lean_object* v_fvarId_2789_; lean_object* v_args_2790_; lean_object* v___x_2791_; 
v_fvarId_2789_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2789_);
v_args_2790_ = lean_ctor_get(v_c_2777_, 1);
lean_inc_ref(v_args_2790_);
lean_dec_ref_known(v_c_2777_, 2);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2791_ = lean_apply_8(v_f_2776_, v_fvarId_2789_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2805_; 
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v___x_2791_, 0);
lean_dec(v_unused_2806_);
v___x_2793_ = v___x_2791_;
v_isShared_2794_ = v_isSharedCheck_2805_;
goto v_resetjp_2792_;
}
else
{
lean_dec(v___x_2791_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2805_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = lean_array_get_size(v_args_2790_);
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_nat_dec_lt(v___x_2795_, v___x_2796_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v_args_2790_);
lean_dec_ref(v_f_2776_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2797_);
v___x_2800_ = v___x_2793_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2797_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
else
{
size_t v___x_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
lean_del_object(v___x_2793_);
v___x_2802_ = ((size_t)0ULL);
v___x_2803_ = lean_usize_of_nat(v___x_2796_);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2775_, v_f_2776_, v_args_2790_, v___x_2802_, v___x_2803_, v___x_2797_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec_ref(v_args_2790_);
return v___x_2804_;
}
}
}
else
{
lean_dec_ref(v_args_2790_);
lean_dec_ref(v_f_2776_);
return v___x_2791_;
}
}
case 4:
{
lean_object* v_cases_2807_; lean_object* v_resultType_2808_; lean_object* v_discr_2809_; lean_object* v_alts_2810_; lean_object* v___x_2811_; 
v_cases_2807_ = lean_ctor_get(v_c_2777_, 0);
lean_inc_ref(v_cases_2807_);
lean_dec_ref_known(v_c_2777_, 1);
v_resultType_2808_ = lean_ctor_get(v_cases_2807_, 1);
lean_inc_ref(v_resultType_2808_);
v_discr_2809_ = lean_ctor_get(v_cases_2807_, 2);
lean_inc(v_discr_2809_);
v_alts_2810_ = lean_ctor_get(v_cases_2807_, 3);
lean_inc_ref(v_alts_2810_);
lean_dec_ref(v_cases_2807_);
lean_inc_ref(v_f_2776_);
v___x_2811_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2776_, v_resultType_2808_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref_known(v___x_2811_, 1);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2812_ = lean_apply_8(v_f_2776_, v_discr_2809_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2812_, 0);
lean_dec(v_unused_2827_);
v___x_2814_ = v___x_2812_;
v_isShared_2815_ = v_isSharedCheck_2826_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v___x_2812_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2826_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2816_ = lean_unsigned_to_nat(0u);
v___x_2817_ = lean_array_get_size(v_alts_2810_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_nat_dec_lt(v___x_2816_, v___x_2817_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2821_; 
lean_dec_ref(v_alts_2810_);
lean_dec_ref(v_f_2776_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2818_);
v___x_2821_ = v___x_2814_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2818_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
else
{
size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
lean_del_object(v___x_2814_);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = lean_usize_of_nat(v___x_2817_);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2775_, v_f_2776_, v_alts_2810_, v___x_2823_, v___x_2824_, v___x_2818_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec_ref(v_alts_2810_);
return v___x_2825_;
}
}
}
else
{
lean_dec_ref(v_alts_2810_);
lean_dec_ref(v_f_2776_);
return v___x_2812_;
}
}
else
{
lean_dec_ref(v_alts_2810_);
lean_dec(v_discr_2809_);
lean_dec_ref(v_f_2776_);
return v___x_2811_;
}
}
case 5:
{
lean_object* v_fvarId_2828_; lean_object* v___x_2829_; 
v_fvarId_2828_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2828_);
lean_dec_ref_known(v_c_2777_, 1);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2829_ = lean_apply_8(v_f_2776_, v_fvarId_2828_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
return v___x_2829_;
}
case 6:
{
lean_object* v_type_2830_; lean_object* v___x_2831_; 
v_type_2830_ = lean_ctor_get(v_c_2777_, 0);
lean_inc_ref(v_type_2830_);
lean_dec_ref_known(v_c_2777_, 1);
v___x_2831_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2776_, v_type_2830_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v___x_2831_;
}
case 7:
{
lean_object* v_fvarId_2832_; lean_object* v_y_2833_; lean_object* v_k_2834_; lean_object* v___x_2835_; 
v_fvarId_2832_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2832_);
v_y_2833_ = lean_ctor_get(v_c_2777_, 2);
lean_inc(v_y_2833_);
v_k_2834_ = lean_ctor_get(v_c_2777_, 3);
lean_inc_ref(v_k_2834_);
lean_dec_ref_known(v_c_2777_, 4);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2835_ = lean_apply_8(v_f_2776_, v_fvarId_2832_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2836_; 
lean_dec_ref_known(v___x_2835_, 1);
lean_inc_ref(v_f_2776_);
v___x_2836_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2776_, v_y_2833_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_dec_ref_known(v___x_2836_, 1);
v_c_2777_ = v_k_2834_;
goto _start;
}
else
{
lean_dec_ref(v_k_2834_);
lean_dec_ref(v_f_2776_);
return v___x_2836_;
}
}
else
{
lean_dec_ref(v_k_2834_);
lean_dec(v_y_2833_);
lean_dec_ref(v_f_2776_);
return v___x_2835_;
}
}
case 8:
{
lean_object* v_fvarId_2838_; lean_object* v_y_2839_; lean_object* v_k_2840_; lean_object* v___x_2841_; 
v_fvarId_2838_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2838_);
v_y_2839_ = lean_ctor_get(v_c_2777_, 2);
lean_inc(v_y_2839_);
v_k_2840_ = lean_ctor_get(v_c_2777_, 3);
lean_inc_ref(v_k_2840_);
lean_dec_ref_known(v_c_2777_, 4);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2841_ = lean_apply_8(v_f_2776_, v_fvarId_2838_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; 
lean_dec_ref_known(v___x_2841_, 1);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2842_ = lean_apply_8(v_f_2776_, v_y_2839_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref_known(v___x_2842_, 1);
v_c_2777_ = v_k_2840_;
goto _start;
}
else
{
lean_dec_ref(v_k_2840_);
lean_dec_ref(v_f_2776_);
return v___x_2842_;
}
}
else
{
lean_dec_ref(v_k_2840_);
lean_dec(v_y_2839_);
lean_dec_ref(v_f_2776_);
return v___x_2841_;
}
}
case 9:
{
lean_object* v_fvarId_2844_; lean_object* v_y_2845_; lean_object* v_ty_2846_; lean_object* v_k_2847_; lean_object* v___x_2848_; 
v_fvarId_2844_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2844_);
v_y_2845_ = lean_ctor_get(v_c_2777_, 3);
lean_inc(v_y_2845_);
v_ty_2846_ = lean_ctor_get(v_c_2777_, 4);
lean_inc_ref(v_ty_2846_);
v_k_2847_ = lean_ctor_get(v_c_2777_, 5);
lean_inc_ref(v_k_2847_);
lean_dec_ref_known(v_c_2777_, 6);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2848_ = lean_apply_8(v_f_2776_, v_fvarId_2844_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref_known(v___x_2848_, 1);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2849_ = lean_apply_8(v_f_2776_, v_y_2845_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; 
lean_dec_ref_known(v___x_2849_, 1);
lean_inc_ref(v_f_2776_);
v___x_2850_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2776_, v_ty_2846_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_dec_ref_known(v___x_2850_, 1);
v_c_2777_ = v_k_2847_;
goto _start;
}
else
{
lean_dec_ref(v_k_2847_);
lean_dec_ref(v_f_2776_);
return v___x_2850_;
}
}
else
{
lean_dec_ref(v_k_2847_);
lean_dec_ref(v_ty_2846_);
lean_dec_ref(v_f_2776_);
return v___x_2849_;
}
}
else
{
lean_dec_ref(v_k_2847_);
lean_dec_ref(v_ty_2846_);
lean_dec(v_y_2845_);
lean_dec_ref(v_f_2776_);
return v___x_2848_;
}
}
case 10:
{
lean_object* v_fvarId_2852_; lean_object* v_k_2853_; lean_object* v___x_2854_; 
v_fvarId_2852_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2852_);
v_k_2853_ = lean_ctor_get(v_c_2777_, 2);
lean_inc_ref(v_k_2853_);
lean_dec_ref_known(v_c_2777_, 3);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2854_ = lean_apply_8(v_f_2776_, v_fvarId_2852_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_dec_ref_known(v___x_2854_, 1);
v_c_2777_ = v_k_2853_;
goto _start;
}
else
{
lean_dec_ref(v_k_2853_);
lean_dec_ref(v_f_2776_);
return v___x_2854_;
}
}
case 11:
{
lean_object* v_fvarId_2856_; lean_object* v_k_2857_; lean_object* v___x_2858_; 
v_fvarId_2856_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2856_);
v_k_2857_ = lean_ctor_get(v_c_2777_, 2);
lean_inc_ref(v_k_2857_);
lean_dec_ref_known(v_c_2777_, 3);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2858_ = lean_apply_8(v_f_2776_, v_fvarId_2856_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_dec_ref_known(v___x_2858_, 1);
v_c_2777_ = v_k_2857_;
goto _start;
}
else
{
lean_dec_ref(v_k_2857_);
lean_dec_ref(v_f_2776_);
return v___x_2858_;
}
}
case 12:
{
lean_object* v_fvarId_2860_; lean_object* v_k_2861_; lean_object* v___x_2862_; 
v_fvarId_2860_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2860_);
v_k_2861_ = lean_ctor_get(v_c_2777_, 3);
lean_inc_ref(v_k_2861_);
lean_dec_ref_known(v_c_2777_, 4);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2862_ = lean_apply_8(v_f_2776_, v_fvarId_2860_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_dec_ref_known(v___x_2862_, 1);
v_c_2777_ = v_k_2861_;
goto _start;
}
else
{
lean_dec_ref(v_k_2861_);
lean_dec_ref(v_f_2776_);
return v___x_2862_;
}
}
case 13:
{
lean_object* v_fvarId_2864_; lean_object* v_k_2865_; lean_object* v___x_2866_; 
v_fvarId_2864_ = lean_ctor_get(v_c_2777_, 0);
lean_inc(v_fvarId_2864_);
v_k_2865_ = lean_ctor_get(v_c_2777_, 1);
lean_inc_ref(v_k_2865_);
lean_dec_ref_known(v_c_2777_, 2);
lean_inc_ref(v_f_2776_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2866_ = lean_apply_8(v_f_2776_, v_fvarId_2864_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_dec_ref_known(v___x_2866_, 1);
v_c_2777_ = v_k_2865_;
goto _start;
}
else
{
lean_dec_ref(v_k_2865_);
lean_dec_ref(v_f_2776_);
return v___x_2866_;
}
}
default: 
{
lean_object* v_decl_2868_; lean_object* v_k_2869_; lean_object* v_params_2870_; lean_object* v_type_2871_; lean_object* v_value_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v_decl_2868_ = lean_ctor_get(v_c_2777_, 0);
lean_inc_ref(v_decl_2868_);
v_k_2869_ = lean_ctor_get(v_c_2777_, 1);
lean_inc_ref(v_k_2869_);
lean_dec_ref(v_c_2777_);
v_params_2870_ = lean_ctor_get(v_decl_2868_, 2);
lean_inc_ref(v_params_2870_);
v_type_2871_ = lean_ctor_get(v_decl_2868_, 3);
lean_inc_ref(v_type_2871_);
v_value_2872_ = lean_ctor_get(v_decl_2868_, 4);
lean_inc_ref(v_value_2872_);
lean_dec_ref(v_decl_2868_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = lean_array_get_size(v_params_2870_);
v___x_2875_ = lean_nat_dec_lt(v___x_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_dec_ref(v_params_2870_);
lean_inc_ref(v_f_2776_);
v___x_2876_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2776_, v_type_2871_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref_known(v___x_2876_, 1);
lean_inc_ref(v_f_2776_);
v___x_2877_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2775_, v_f_2776_, v_value_2872_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_dec_ref_known(v___x_2877_, 1);
v_c_2777_ = v_k_2869_;
goto _start;
}
else
{
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_f_2776_);
return v___x_2877_;
}
}
else
{
lean_dec_ref(v_value_2872_);
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_f_2776_);
return v___x_2876_;
}
}
else
{
lean_object* v___x_2879_; size_t v___x_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = ((size_t)0ULL);
v___x_2881_ = lean_usize_of_nat(v___x_2874_);
lean_inc_ref(v_f_2776_);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2775_, v_f_2776_, v_params_2870_, v___x_2880_, v___x_2881_, v___x_2879_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec_ref(v_params_2870_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v___x_2883_; 
lean_dec_ref_known(v___x_2882_, 1);
lean_inc_ref(v_f_2776_);
v___x_2883_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2776_, v_type_2871_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; 
lean_dec_ref_known(v___x_2883_, 1);
lean_inc_ref(v_f_2776_);
v___x_2884_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2775_, v_f_2776_, v_value_2872_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_dec_ref_known(v___x_2884_, 1);
v_c_2777_ = v_k_2869_;
goto _start;
}
else
{
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_f_2776_);
return v___x_2884_;
}
}
else
{
lean_dec_ref(v_value_2872_);
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_f_2776_);
return v___x_2883_;
}
}
else
{
lean_dec_ref(v_value_2872_);
lean_dec_ref(v_type_2871_);
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_f_2776_);
return v___x_2882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2886_, lean_object* v_f_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2886_, v_f_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_2897_, lean_object* v_f_2898_, lean_object* v_as_2899_, lean_object* v_i_2900_, lean_object* v_stop_2901_, lean_object* v_b_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
uint8_t v_pu_boxed_2910_; size_t v_i_boxed_2911_; size_t v_stop_boxed_2912_; lean_object* v_res_2913_; 
v_pu_boxed_2910_ = lean_unbox(v_pu_2897_);
v_i_boxed_2911_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_stop_boxed_2912_ = lean_unbox_usize(v_stop_2901_);
lean_dec(v_stop_2901_);
v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_2910_, v_f_2898_, v_as_2899_, v_i_boxed_2911_, v_stop_boxed_2912_, v_b_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v_as_2899_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_2914_, lean_object* v_f_2915_, lean_object* v_c_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
uint8_t v_pu_boxed_2924_; lean_object* v_res_2925_; 
v_pu_boxed_2924_ = lean_unbox(v_pu_2914_);
v_res_2925_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_2924_, v_f_2915_, v_c_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec(v___y_2917_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_2926_, lean_object* v_f_2927_, lean_object* v_decl_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_params_2936_; lean_object* v_type_2937_; lean_object* v_value_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v_params_2936_ = lean_ctor_get(v_decl_2928_, 2);
lean_inc_ref(v_params_2936_);
v_type_2937_ = lean_ctor_get(v_decl_2928_, 3);
lean_inc_ref(v_type_2937_);
v_value_2938_ = lean_ctor_get(v_decl_2928_, 4);
lean_inc_ref(v_value_2938_);
lean_dec_ref(v_decl_2928_);
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = lean_array_get_size(v_params_2936_);
v___x_2941_ = lean_nat_dec_lt(v___x_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref(v_params_2936_);
lean_inc_ref(v_f_2927_);
v___x_2942_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2927_, v_type_2937_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref_known(v___x_2942_, 1);
v___x_2943_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2926_, v_f_2927_, v_value_2938_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v___x_2943_;
}
else
{
lean_dec_ref(v_value_2938_);
lean_dec_ref(v_f_2927_);
return v___x_2942_;
}
}
else
{
lean_object* v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_of_nat(v___x_2940_);
lean_inc_ref(v_f_2927_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2926_, v_f_2927_, v_params_2936_, v___x_2945_, v___x_2946_, v___x_2944_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec_ref(v_params_2936_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref_known(v___x_2947_, 1);
lean_inc_ref(v_f_2927_);
v___x_2948_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2927_, v_type_2937_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref_known(v___x_2948_, 1);
v___x_2949_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2926_, v_f_2927_, v_value_2938_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v___x_2949_;
}
else
{
lean_dec_ref(v_value_2938_);
lean_dec_ref(v_f_2927_);
return v___x_2948_;
}
}
else
{
lean_dec_ref(v_value_2938_);
lean_dec_ref(v_type_2937_);
lean_dec_ref(v_f_2927_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_2950_, lean_object* v_f_2951_, lean_object* v_decl_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
uint8_t v_pu_boxed_2960_; lean_object* v_res_2961_; 
v_pu_boxed_2960_ = lean_unbox(v_pu_2950_);
v_res_2961_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_2960_, v_f_2951_, v_decl_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2953_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_panic_fn_borrowed(v___x_2963_, v_msg_2962_);
return v___x_2964_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2968_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_2969_ = lean_unsigned_to_nat(11u);
v___x_2970_ = lean_unsigned_to_nat(163u);
v___x_2971_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_2972_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_2973_ = l_mkPanicMessageWithDecl(v___x_2972_, v___x_2971_, v___x_2970_, v___x_2969_, v___x_2968_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_2974_, lean_object* v_x_2975_){
_start:
{
if (lean_obj_tag(v_x_2975_) == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_2977_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_2976_);
return v___x_2977_;
}
else
{
lean_object* v_key_2978_; lean_object* v_value_2979_; lean_object* v_tail_2980_; uint8_t v___x_2981_; 
v_key_2978_ = lean_ctor_get(v_x_2975_, 0);
v_value_2979_ = lean_ctor_get(v_x_2975_, 1);
v_tail_2980_ = lean_ctor_get(v_x_2975_, 2);
v___x_2981_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2978_, v_a_2974_);
if (v___x_2981_ == 0)
{
v_x_2975_ = v_tail_2980_;
goto _start;
}
else
{
lean_inc(v_value_2979_);
return v_value_2979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_2983_, v_x_2984_);
lean_dec(v_x_2984_);
lean_dec(v_a_2983_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_buckets_2988_; lean_object* v___x_2989_; uint64_t v___x_2990_; uint64_t v___x_2991_; uint64_t v___x_2992_; uint64_t v_fold_2993_; uint64_t v___x_2994_; uint64_t v___x_2995_; uint64_t v___x_2996_; size_t v___x_2997_; size_t v___x_2998_; size_t v___x_2999_; size_t v___x_3000_; size_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_buckets_2988_ = lean_ctor_get(v_m_2986_, 1);
v___x_2989_ = lean_array_get_size(v_buckets_2988_);
v___x_2990_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2987_);
v___x_2991_ = 32ULL;
v___x_2992_ = lean_uint64_shift_right(v___x_2990_, v___x_2991_);
v_fold_2993_ = lean_uint64_xor(v___x_2990_, v___x_2992_);
v___x_2994_ = 16ULL;
v___x_2995_ = lean_uint64_shift_right(v_fold_2993_, v___x_2994_);
v___x_2996_ = lean_uint64_xor(v_fold_2993_, v___x_2995_);
v___x_2997_ = lean_uint64_to_usize(v___x_2996_);
v___x_2998_ = lean_usize_of_nat(v___x_2989_);
v___x_2999_ = ((size_t)1ULL);
v___x_3000_ = lean_usize_sub(v___x_2998_, v___x_2999_);
v___x_3001_ = lean_usize_land(v___x_2997_, v___x_3000_);
v___x_3002_ = lean_array_uget_borrowed(v_buckets_2988_, v___x_3001_);
v___x_3003_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_2987_, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3004_, v_a_3005_);
lean_dec(v_a_3005_);
lean_dec_ref(v_m_3004_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___y_3017_; uint8_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = 0;
v___x_3043_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3008_))
{
case 0:
{
lean_object* v_decl_3044_; lean_object* v___x_3045_; 
v_decl_3044_ = lean_ctor_get(v_decl_3008_, 0);
lean_inc_ref(v_decl_3044_);
v___x_3045_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3042_, v___x_3043_, v_decl_3044_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3017_ = v___x_3045_;
goto v___jp_3016_;
}
case 1:
{
lean_object* v_decl_3046_; lean_object* v___x_3047_; 
v_decl_3046_ = lean_ctor_get(v_decl_3008_, 0);
lean_inc_ref(v_decl_3046_);
v___x_3047_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3042_, v___x_3043_, v_decl_3046_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3017_ = v___x_3047_;
goto v___jp_3016_;
}
case 2:
{
lean_object* v_decl_3048_; lean_object* v___x_3049_; 
v_decl_3048_ = lean_ctor_get(v_decl_3008_, 0);
lean_inc_ref(v_decl_3048_);
v___x_3049_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3042_, v___x_3043_, v_decl_3048_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3017_ = v___x_3049_;
goto v___jp_3016_;
}
case 3:
{
lean_object* v_fvarId_3050_; lean_object* v_y_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_fvarId_3050_ = lean_ctor_get(v_decl_3008_, 0);
v_y_3051_ = lean_ctor_get(v_decl_3008_, 2);
lean_inc(v_fvarId_3050_);
v___x_3052_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3050_, v_a_3009_);
lean_dec_ref(v___x_3052_);
lean_inc(v_y_3051_);
v___x_3053_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3043_, v_y_3051_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3017_ = v___x_3053_;
goto v___jp_3016_;
}
case 4:
{
lean_object* v_fvarId_3054_; lean_object* v_y_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v_fvarId_3054_ = lean_ctor_get(v_decl_3008_, 0);
v_y_3055_ = lean_ctor_get(v_decl_3008_, 2);
lean_inc(v_fvarId_3054_);
v___x_3056_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3054_, v_a_3009_);
lean_dec_ref(v___x_3056_);
lean_inc(v_y_3055_);
v___x_3057_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3055_, v_a_3009_);
v___y_3017_ = v___x_3057_;
goto v___jp_3016_;
}
case 5:
{
lean_object* v_fvarId_3058_; lean_object* v_y_3059_; lean_object* v_ty_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_fvarId_3058_ = lean_ctor_get(v_decl_3008_, 0);
v_y_3059_ = lean_ctor_get(v_decl_3008_, 3);
v_ty_3060_ = lean_ctor_get(v_decl_3008_, 4);
lean_inc(v_fvarId_3058_);
v___x_3061_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3058_, v_a_3009_);
lean_dec_ref(v___x_3061_);
lean_inc(v_y_3059_);
v___x_3062_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3059_, v_a_3009_);
lean_dec_ref(v___x_3062_);
lean_inc_ref(v_ty_3060_);
v___x_3063_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3043_, v_ty_3060_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3017_ = v___x_3063_;
goto v___jp_3016_;
}
default: 
{
lean_object* v_fvarId_3064_; lean_object* v___x_3065_; 
v_fvarId_3064_ = lean_ctor_get(v_decl_3008_, 0);
lean_inc(v_fvarId_3064_);
v___x_3065_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3064_, v_a_3009_);
v___y_3017_ = v___x_3065_;
goto v___jp_3016_;
}
}
v___jp_3016_:
{
if (lean_obj_tag(v___y_3017_) == 0)
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3040_; 
v_isSharedCheck_3040_ = !lean_is_exclusive(v___y_3017_);
if (v_isSharedCheck_3040_ == 0)
{
lean_object* v_unused_3041_; 
v_unused_3041_ = lean_ctor_get(v___y_3017_, 0);
lean_dec(v_unused_3041_);
v___x_3019_ = v___y_3017_;
v_isShared_3020_ = v_isSharedCheck_3040_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v___y_3017_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3040_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v_decision_3022_; lean_object* v_newArms_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3039_; 
v___x_3021_ = lean_st_ref_take(v_a_3009_);
v_decision_3022_ = lean_ctor_get(v___x_3021_, 0);
v_newArms_3023_ = lean_ctor_get(v___x_3021_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3025_ = v___x_3021_;
v_isShared_3026_ = v_isSharedCheck_3039_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_newArms_3023_);
lean_inc(v_decision_3022_);
lean_dec(v___x_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3039_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_box(2);
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3023_, v___x_3028_);
v___x_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_decl_3008_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3023_, v___x_3028_, v___x_3030_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 1, v___x_3031_);
v___x_3033_ = v___x_3025_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_decision_3022_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3034_ = lean_st_ref_put(v_a_3009_, v___x_3033_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3027_);
v___x_3036_ = v___x_3019_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3027_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3008_);
return v___y_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec(v_a_3067_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3075_, lean_object* v_f_3076_, lean_object* v_arg_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3076_, v_arg_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3086_, lean_object* v_f_3087_, lean_object* v_arg_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
uint8_t v_pu_boxed_3096_; lean_object* v_res_3097_; 
v_pu_boxed_3096_ = lean_unbox(v_pu_3086_);
v_res_3097_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3096_, v_f_3087_, v_arg_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec(v___y_3089_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3098_, lean_object* v_f_3099_, lean_object* v_param_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3099_, v_param_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3109_, lean_object* v_f_3110_, lean_object* v_param_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
uint8_t v_pu_boxed_3119_; lean_object* v_res_3120_; 
v_pu_boxed_3119_ = lean_unbox(v_pu_3109_);
v_res_3120_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3119_, v_f_3110_, v_param_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec(v___y_3112_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3121_, lean_object* v_alt_3122_, lean_object* v_f_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3122_, v_f_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3132_, lean_object* v_alt_3133_, lean_object* v_f_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_pu_boxed_3142_; lean_object* v_res_3143_; 
v_pu_boxed_3142_ = lean_unbox(v_pu_3132_);
v_res_3143_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3142_, v_alt_3133_, v_f_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec(v___y_3135_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3144_, lean_object* v_arm_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v_decision_3165_; lean_object* v___x_3166_; 
v___x_3148_ = lean_st_ref_get(v_a_3146_);
v_decision_3165_ = lean_ctor_get(v___x_3148_, 0);
lean_inc_ref(v_decision_3165_);
lean_dec(v___x_3148_);
v___x_3166_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3165_, v_fvar_3144_);
lean_dec_ref(v_decision_3165_);
if (lean_obj_tag(v___x_3166_) == 1)
{
lean_object* v_val_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3194_; 
v_val_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3194_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_val_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3194_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3171_ = lean_box(3);
v___x_3172_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3167_, v___x_3171_);
if (v___x_3172_ == 0)
{
uint8_t v___x_3173_; 
v___x_3173_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3167_, v_arm_3145_);
lean_dec(v_arm_3145_);
lean_dec(v_val_3167_);
if (v___x_3173_ == 0)
{
lean_del_object(v___x_3169_);
goto v___jp_3149_;
}
else
{
if (v___x_3172_ == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
lean_dec(v_fvar_3144_);
v___x_3174_ = lean_box(0);
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3174_);
v___x_3176_ = v___x_3169_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
else
{
lean_del_object(v___x_3169_);
goto v___jp_3149_;
}
}
}
else
{
lean_object* v___x_3178_; lean_object* v_decision_3179_; lean_object* v_newArms_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_val_3167_);
v___x_3178_ = lean_st_ref_take(v_a_3146_);
v_decision_3179_ = lean_ctor_get(v___x_3178_, 0);
v_newArms_3180_ = lean_ctor_get(v___x_3178_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3182_ = v___x_3178_;
v_isShared_3183_ = v_isSharedCheck_3193_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_newArms_3180_);
lean_inc(v_decision_3179_);
lean_dec(v___x_3178_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3193_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3184_ = lean_box(0);
v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3179_, v_fvar_3144_, v_arm_3145_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3185_);
v___x_3187_ = v___x_3182_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_newArms_3180_);
v___x_3187_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_st_ref_put(v_a_3146_, v___x_3187_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3184_);
v___x_3190_ = v___x_3169_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3184_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_dec(v___x_3166_);
lean_dec(v_arm_3145_);
lean_dec(v_fvar_3144_);
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
v___jp_3149_:
{
lean_object* v___x_3150_; lean_object* v_decision_3151_; lean_object* v_newArms_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3164_; 
v___x_3150_ = lean_st_ref_take(v_a_3146_);
v_decision_3151_ = lean_ctor_get(v___x_3150_, 0);
v_newArms_3152_ = lean_ctor_get(v___x_3150_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3154_ = v___x_3150_;
v_isShared_3155_ = v_isSharedCheck_3164_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_newArms_3152_);
lean_inc(v_decision_3151_);
lean_dec(v___x_3150_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3164_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_box(2);
v___x_3158_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3151_, v_fvar_3144_, v___x_3157_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3158_);
v___x_3160_ = v___x_3154_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_newArms_3152_);
v___x_3160_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_st_ref_put(v_a_3146_, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3156_);
return v___x_3162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3197_, lean_object* v_arm_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3197_, v_arm_3198_, v_a_3199_);
lean_dec(v_a_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3202_, lean_object* v_arm_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3202_, v_arm_3203_, v_a_3204_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3212_, lean_object* v_arm_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3212_, v_arm_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec(v_a_3214_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3222_, lean_object* v_x_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3223_, v___x_3222_, v___y_3224_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3232_, lean_object* v_x_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3232_, v_x_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec(v___y_3234_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3242_){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3244_ = lean_panic_fn_borrowed(v___x_3243_, v_msg_3242_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3245_, lean_object* v_x_3246_){
_start:
{
if (lean_obj_tag(v_x_3246_) == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3248_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3247_);
return v___x_3248_;
}
else
{
lean_object* v_key_3249_; lean_object* v_value_3250_; lean_object* v_tail_3251_; uint8_t v___x_3252_; 
v_key_3249_ = lean_ctor_get(v_x_3246_, 0);
v_value_3250_ = lean_ctor_get(v_x_3246_, 1);
v_tail_3251_ = lean_ctor_get(v_x_3246_, 2);
v___x_3252_ = l_Lean_instBEqFVarId_beq(v_key_3249_, v_a_3245_);
if (v___x_3252_ == 0)
{
v_x_3246_ = v_tail_3251_;
goto _start;
}
else
{
lean_inc(v_value_3250_);
return v_value_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3254_, v_x_3255_);
lean_dec(v_x_3255_);
lean_dec(v_a_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_buckets_3259_; lean_object* v___x_3260_; uint64_t v___x_3261_; uint64_t v___x_3262_; uint64_t v___x_3263_; uint64_t v_fold_3264_; uint64_t v___x_3265_; uint64_t v___x_3266_; uint64_t v___x_3267_; size_t v___x_3268_; size_t v___x_3269_; size_t v___x_3270_; size_t v___x_3271_; size_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_buckets_3259_ = lean_ctor_get(v_m_3257_, 1);
v___x_3260_ = lean_array_get_size(v_buckets_3259_);
v___x_3261_ = l_Lean_instHashableFVarId_hash(v_a_3258_);
v___x_3262_ = 32ULL;
v___x_3263_ = lean_uint64_shift_right(v___x_3261_, v___x_3262_);
v_fold_3264_ = lean_uint64_xor(v___x_3261_, v___x_3263_);
v___x_3265_ = 16ULL;
v___x_3266_ = lean_uint64_shift_right(v_fold_3264_, v___x_3265_);
v___x_3267_ = lean_uint64_xor(v_fold_3264_, v___x_3266_);
v___x_3268_ = lean_uint64_to_usize(v___x_3267_);
v___x_3269_ = lean_usize_of_nat(v___x_3260_);
v___x_3270_ = ((size_t)1ULL);
v___x_3271_ = lean_usize_sub(v___x_3269_, v___x_3270_);
v___x_3272_ = lean_usize_land(v___x_3268_, v___x_3271_);
v___x_3273_ = lean_array_uget_borrowed(v_buckets_3259_, v___x_3272_);
v___x_3274_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3258_, v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_m_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v___x_3286_; lean_object* v_decision_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3344_; 
v___x_3286_ = lean_st_ref_get(v_a_3279_);
v_decision_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v___x_3286_, 1);
lean_dec(v_unused_3345_);
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3344_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_decision_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3344_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___y_3295_; lean_object* v___f_3321_; 
v___x_3291_ = 0;
v___x_3292_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3278_);
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3287_, v___x_3292_);
lean_dec(v___x_3292_);
lean_dec_ref(v_decision_3287_);
lean_inc(v___x_3293_);
v___f_3321_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3321_, 0, v___x_3293_);
switch(lean_obj_tag(v_decl_3278_))
{
case 0:
{
lean_object* v_decl_3322_; lean_object* v___x_3323_; 
v_decl_3322_ = lean_ctor_get(v_decl_3278_, 0);
lean_inc_ref(v_decl_3322_);
v___x_3323_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3291_, v___f_3321_, v_decl_3322_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
v___y_3295_ = v___x_3323_;
goto v___jp_3294_;
}
case 1:
{
lean_object* v_decl_3324_; lean_object* v___x_3325_; 
v_decl_3324_ = lean_ctor_get(v_decl_3278_, 0);
lean_inc_ref(v_decl_3324_);
v___x_3325_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3291_, v___f_3321_, v_decl_3324_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
v___y_3295_ = v___x_3325_;
goto v___jp_3294_;
}
case 2:
{
lean_object* v_decl_3326_; lean_object* v___x_3327_; 
v_decl_3326_ = lean_ctor_get(v_decl_3278_, 0);
lean_inc_ref(v_decl_3326_);
v___x_3327_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3291_, v___f_3321_, v_decl_3326_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
v___y_3295_ = v___x_3327_;
goto v___jp_3294_;
}
case 3:
{
lean_object* v_fvarId_3328_; lean_object* v_y_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_fvarId_3328_ = lean_ctor_get(v_decl_3278_, 0);
v_y_3329_ = lean_ctor_get(v_decl_3278_, 2);
lean_inc(v___x_3293_);
lean_inc(v_fvarId_3328_);
v___x_3330_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3328_, v___x_3293_, v_a_3279_);
lean_dec_ref(v___x_3330_);
lean_inc(v_y_3329_);
v___x_3331_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3321_, v_y_3329_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
v___y_3295_ = v___x_3331_;
goto v___jp_3294_;
}
case 4:
{
lean_object* v_fvarId_3332_; lean_object* v_y_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v___f_3321_);
v_fvarId_3332_ = lean_ctor_get(v_decl_3278_, 0);
v_y_3333_ = lean_ctor_get(v_decl_3278_, 2);
lean_inc_n(v___x_3293_, 2);
lean_inc(v_fvarId_3332_);
v___x_3334_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3332_, v___x_3293_, v_a_3279_);
lean_dec_ref(v___x_3334_);
lean_inc(v_y_3333_);
v___x_3335_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3333_, v___x_3293_, v_a_3279_);
v___y_3295_ = v___x_3335_;
goto v___jp_3294_;
}
case 5:
{
lean_object* v_fvarId_3336_; lean_object* v_y_3337_; lean_object* v_ty_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_fvarId_3336_ = lean_ctor_get(v_decl_3278_, 0);
v_y_3337_ = lean_ctor_get(v_decl_3278_, 3);
v_ty_3338_ = lean_ctor_get(v_decl_3278_, 4);
lean_inc_n(v___x_3293_, 2);
lean_inc(v_fvarId_3336_);
v___x_3339_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3336_, v___x_3293_, v_a_3279_);
lean_dec_ref(v___x_3339_);
lean_inc(v_y_3337_);
v___x_3340_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3337_, v___x_3293_, v_a_3279_);
lean_dec_ref(v___x_3340_);
lean_inc_ref(v_ty_3338_);
v___x_3341_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3321_, v_ty_3338_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
v___y_3295_ = v___x_3341_;
goto v___jp_3294_;
}
default: 
{
lean_object* v_fvarId_3342_; lean_object* v___x_3343_; 
lean_dec_ref(v___f_3321_);
v_fvarId_3342_ = lean_ctor_get(v_decl_3278_, 0);
lean_inc(v___x_3293_);
lean_inc(v_fvarId_3342_);
v___x_3343_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3342_, v___x_3293_, v_a_3279_);
v___y_3295_ = v___x_3343_;
goto v___jp_3294_;
}
}
v___jp_3294_:
{
if (lean_obj_tag(v___y_3295_) == 0)
{
lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3319_; 
v_isSharedCheck_3319_ = !lean_is_exclusive(v___y_3295_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v___y_3295_, 0);
lean_dec(v_unused_3320_);
v___x_3297_ = v___y_3295_;
v_isShared_3298_ = v_isSharedCheck_3319_;
goto v_resetjp_3296_;
}
else
{
lean_dec(v___y_3295_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3319_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v_decision_3300_; lean_object* v_newArms_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3318_; 
v___x_3299_ = lean_st_ref_take(v_a_3279_);
v_decision_3300_ = lean_ctor_get(v___x_3299_, 0);
v_newArms_3301_ = lean_ctor_get(v___x_3299_, 1);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3303_ = v___x_3299_;
v_isShared_3304_ = v_isSharedCheck_3318_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_newArms_3301_);
lean_inc(v_decision_3300_);
lean_dec(v___x_3299_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3318_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3301_, v___x_3293_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 1);
lean_ctor_set(v___x_3289_, 1, v___x_3306_);
lean_ctor_set(v___x_3289_, 0, v_decl_3278_);
v___x_3308_ = v___x_3289_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_decl_3278_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3301_, v___x_3293_, v___x_3308_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 1, v___x_3309_);
v___x_3311_ = v___x_3303_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_decision_3300_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3312_ = lean_st_ref_put(v_a_3279_, v___x_3311_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3305_);
v___x_3314_ = v___x_3297_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3305_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3293_);
lean_del_object(v___x_3289_);
lean_dec_ref(v_decl_3278_);
return v___y_3295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec(v_a_3347_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
if (lean_obj_tag(v_as_x27_3355_) == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_b_3356_);
return v___x_3364_;
}
else
{
lean_object* v_head_3365_; lean_object* v_tail_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v_decision_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_head_3365_ = lean_ctor_get(v_as_x27_3355_, 0);
v_tail_3366_ = lean_ctor_get(v_as_x27_3355_, 1);
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_st_ref_get(v___y_3357_);
v_decision_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc_ref(v_decision_3369_);
lean_dec(v___x_3368_);
v___x_3370_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3365_);
v___x_3371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3369_, v___x_3370_);
lean_dec(v___x_3370_);
lean_dec_ref(v_decision_3369_);
v___x_3372_ = lean_box(3);
v___x_3373_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3371_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = lean_box(2);
v___x_3375_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3371_, v___x_3374_);
lean_dec(v___x_3371_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; 
lean_inc(v_head_3365_);
v___x_3376_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3365_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_dec_ref_known(v___x_3376_, 1);
v_as_x27_3355_ = v_tail_3366_;
v_b_3356_ = v___x_3367_;
goto _start;
}
else
{
return v___x_3376_;
}
}
else
{
lean_object* v___x_3378_; 
lean_inc(v_head_3365_);
v___x_3378_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3365_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec_ref_known(v___x_3378_, 1);
v_as_x27_3355_ = v_tail_3366_;
v_b_3356_ = v___x_3367_;
goto _start;
}
else
{
return v___x_3378_;
}
}
}
else
{
uint8_t v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v___x_3371_);
v___x_3380_ = 0;
v___x_3381_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3380_, v_head_3365_, v___y_3360_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_dec_ref_known(v___x_3381_, 1);
v_as_x27_3355_ = v_tail_3366_;
v_b_3356_ = v___x_3367_;
goto _start;
}
else
{
return v___x_3381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3383_, lean_object* v_b_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3383_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec(v_as_x27_3383_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_box(0);
v___x_3401_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3394_, v___x_3400_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v___x_3401_, 0);
lean_dec(v_unused_3409_);
v___x_3403_ = v___x_3401_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v___x_3401_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3400_);
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3400_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec(v_a_3410_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3418_, lean_object* v_as_x27_3419_, lean_object* v_b_3420_, lean_object* v_a_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3419_, v_b_3420_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_3430_, lean_object* v_as_x27_3431_, lean_object* v_b_3432_, lean_object* v_a_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3430_, v_as_x27_3431_, v_b_3432_, v_a_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec(v_as_x27_3431_);
lean_dec(v_as_3430_);
return v_res_3441_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3442_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
lean_ctor_set(v___x_3447_, 2, v___x_3446_);
lean_ctor_set(v___x_3447_, 3, v___x_3446_);
lean_ctor_set(v___x_3447_, 4, v___x_3445_);
lean_ctor_set(v___x_3447_, 5, v___x_3445_);
lean_ctor_set(v___x_3447_, 6, v___x_3445_);
lean_ctor_set(v___x_3447_, 7, v___x_3445_);
lean_ctor_set(v___x_3447_, 8, v___x_3445_);
lean_ctor_set(v___x_3447_, 9, v___x_3445_);
lean_ctor_set(v___x_3447_, 10, v___x_3445_);
return v___x_3447_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3448_; double v___x_3449_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = lean_float_of_nat(v___x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3453_, lean_object* v_msg_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_ref_3460_; lean_object* v___x_3461_; lean_object* v_env_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_ref_3460_ = lean_ctor_get(v___y_3457_, 2);
v___x_3461_ = lean_st_ref_get(v___y_3458_);
v_env_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc_ref(v_env_3462_);
lean_dec(v___x_3461_);
v___x_3463_ = lean_st_ref_get(v___y_3456_);
v___x_3464_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3455_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3524_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3524_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3524_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_lctx_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3522_; 
v_lctx_3469_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; 
v_unused_3523_ = lean_ctor_get(v___x_3463_, 1);
lean_dec(v_unused_3523_);
v___x_3471_ = v___x_3463_;
v_isShared_3472_ = v_isSharedCheck_3522_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_lctx_3469_);
lean_dec(v___x_3463_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3522_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3473_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
v___x_3474_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3469_, v___x_3473_);
lean_dec_ref(v_lctx_3469_);
v___x_3475_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3457_);
v___x_3476_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3477_, 0, v_env_3462_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
lean_ctor_set(v___x_3477_, 2, v___x_3474_);
lean_ctor_set(v___x_3477_, 3, v___x_3475_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 3);
lean_ctor_set(v___x_3471_, 1, v_msg_3454_);
lean_ctor_set(v___x_3471_, 0, v___x_3477_);
v___x_3479_ = v___x_3471_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_msg_3454_);
v___x_3479_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v_traceState_3481_; lean_object* v_env_3482_; lean_object* v_nextMacroScope_3483_; lean_object* v_ngen_3484_; lean_object* v_auxDeclNGen_3485_; lean_object* v_cache_3486_; lean_object* v_recordedDeps_3487_; lean_object* v_messages_3488_; lean_object* v_infoState_3489_; lean_object* v_snapshotTasks_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3520_; 
v___x_3480_ = lean_st_ref_take(v___y_3458_);
v_traceState_3481_ = lean_ctor_get(v___x_3480_, 4);
v_env_3482_ = lean_ctor_get(v___x_3480_, 0);
v_nextMacroScope_3483_ = lean_ctor_get(v___x_3480_, 1);
v_ngen_3484_ = lean_ctor_get(v___x_3480_, 2);
v_auxDeclNGen_3485_ = lean_ctor_get(v___x_3480_, 3);
v_cache_3486_ = lean_ctor_get(v___x_3480_, 5);
v_recordedDeps_3487_ = lean_ctor_get(v___x_3480_, 6);
v_messages_3488_ = lean_ctor_get(v___x_3480_, 7);
v_infoState_3489_ = lean_ctor_get(v___x_3480_, 8);
v_snapshotTasks_3490_ = lean_ctor_get(v___x_3480_, 9);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3492_ = v___x_3480_;
v_isShared_3493_ = v_isSharedCheck_3520_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snapshotTasks_3490_);
lean_inc(v_infoState_3489_);
lean_inc(v_messages_3488_);
lean_inc(v_recordedDeps_3487_);
lean_inc(v_cache_3486_);
lean_inc(v_traceState_3481_);
lean_inc(v_auxDeclNGen_3485_);
lean_inc(v_ngen_3484_);
lean_inc(v_nextMacroScope_3483_);
lean_inc(v_env_3482_);
lean_dec(v___x_3480_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3520_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
uint64_t v_tid_3494_; lean_object* v_traces_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3519_; 
v_tid_3494_ = lean_ctor_get_uint64(v_traceState_3481_, sizeof(void*)*1);
v_traces_3495_ = lean_ctor_get(v_traceState_3481_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_traceState_3481_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3497_ = v_traceState_3481_;
v_isShared_3498_ = v_isSharedCheck_3519_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_traces_3495_);
lean_dec(v_traceState_3481_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3519_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; double v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3499_ = lean_box(0);
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3502_ = 0;
v___x_3503_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3504_, 0, v_cls_3453_);
lean_ctor_set(v___x_3504_, 1, v___x_3500_);
lean_ctor_set(v___x_3504_, 2, v___x_3503_);
lean_ctor_set_float(v___x_3504_, sizeof(void*)*3, v___x_3501_);
lean_ctor_set_float(v___x_3504_, sizeof(void*)*3 + 8, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*3 + 16, v___x_3502_);
v___x_3505_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3506_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3479_);
lean_ctor_set(v___x_3506_, 2, v___x_3505_);
lean_inc(v_ref_3460_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v_ref_3460_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = l_Lean_PersistentArray_push___redArg(v_traces_3495_, v___x_3507_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3508_);
v___x_3510_ = v___x_3497_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3508_);
lean_ctor_set_uint64(v_reuseFailAlloc_3518_, sizeof(void*)*1, v_tid_3494_);
v___x_3510_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v___x_3510_);
v___x_3512_ = v___x_3492_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_env_3482_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_nextMacroScope_3483_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_ngen_3484_);
lean_ctor_set(v_reuseFailAlloc_3517_, 3, v_auxDeclNGen_3485_);
lean_ctor_set(v_reuseFailAlloc_3517_, 4, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3517_, 5, v_cache_3486_);
lean_ctor_set(v_reuseFailAlloc_3517_, 6, v_recordedDeps_3487_);
lean_ctor_set(v_reuseFailAlloc_3517_, 7, v_messages_3488_);
lean_ctor_set(v_reuseFailAlloc_3517_, 8, v_infoState_3489_);
lean_ctor_set(v_reuseFailAlloc_3517_, 9, v_snapshotTasks_3490_);
v___x_3512_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = lean_st_ref_put(v___y_3458_, v___x_3512_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3499_);
v___x_3515_ = v___x_3467_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3499_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
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
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v___x_3463_);
lean_dec_ref(v_env_3462_);
lean_dec_ref(v_msg_3454_);
lean_dec(v_cls_3453_);
v_a_3525_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3464_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3464_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3533_, lean_object* v_msg_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3533_, v_msg_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3541_, lean_object* v_msg_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3541_, v_msg_3542_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3550_, lean_object* v_msg_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3550_, v_msg_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
return v_res_3558_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3568_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3569_ = l_Lean_Name_append(v___x_3568_, v___x_3567_);
return v___x_3569_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3572_ = l_Lean_stringToMessageData(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3575_ = l_Lean_stringToMessageData(v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
switch(lean_obj_tag(v_code_3576_))
{
case 0:
{
lean_object* v_decl_3583_; lean_object* v_k_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_decl_3583_ = lean_ctor_get(v_code_3576_, 0);
lean_inc_ref(v_decl_3583_);
v_k_3584_ = lean_ctor_get(v_code_3576_, 1);
lean_inc_ref(v_k_3584_);
lean_dec_ref_known(v_code_3576_, 2);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v_decl_3583_);
v___x_3586_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3586_, 0, v_k_3584_);
v___x_3587_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3585_, v___x_3586_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
return v___x_3587_;
}
case 1:
{
lean_object* v_decl_3588_; lean_object* v_k_3589_; lean_object* v_params_3590_; lean_object* v_type_3591_; lean_object* v_value_3592_; uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_decl_3588_ = lean_ctor_get(v_code_3576_, 0);
lean_inc_ref(v_decl_3588_);
v_k_3589_ = lean_ctor_get(v_code_3576_, 1);
lean_inc_ref(v_k_3589_);
lean_dec_ref_known(v_code_3576_, 2);
v_params_3590_ = lean_ctor_get(v_decl_3588_, 2);
lean_inc_ref(v_params_3590_);
v_type_3591_ = lean_ctor_get(v_decl_3588_, 3);
lean_inc_ref(v_type_3591_);
v_value_3592_ = lean_ctor_get(v_decl_3588_, 4);
v___x_3593_ = 0;
lean_inc_ref(v_value_3592_);
v___x_3594_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3594_, 0, v_value_3592_);
v___x_3595_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3594_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3615_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3615_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3615_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; 
v___x_3600_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3593_, v_decl_3588_, v_type_3591_, v_params_3590_, v_a_3596_, v_a_3579_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
if (v_isShared_3599_ == 0)
{
lean_ctor_set_tag(v___x_3598_, 1);
lean_ctor_set(v___x_3598_, 0, v_a_3601_);
v___x_3603_ = v___x_3598_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3601_);
v___x_3603_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3604_, 0, v_k_3589_);
v___x_3605_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3603_, v___x_3604_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
return v___x_3605_;
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_del_object(v___x_3598_);
lean_dec_ref(v_k_3589_);
v_a_3607_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3600_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3600_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3591_);
lean_dec_ref(v_params_3590_);
lean_dec_ref(v_k_3589_);
lean_dec_ref(v_decl_3588_);
return v___x_3595_;
}
}
case 2:
{
lean_object* v_decl_3616_; lean_object* v_k_3617_; lean_object* v_params_3618_; lean_object* v_type_3619_; lean_object* v_value_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_decl_3616_ = lean_ctor_get(v_code_3576_, 0);
lean_inc_ref(v_decl_3616_);
v_k_3617_ = lean_ctor_get(v_code_3576_, 1);
lean_inc_ref(v_k_3617_);
lean_dec_ref_known(v_code_3576_, 2);
v_params_3618_ = lean_ctor_get(v_decl_3616_, 2);
lean_inc_ref(v_params_3618_);
v_type_3619_ = lean_ctor_get(v_decl_3616_, 3);
lean_inc_ref(v_type_3619_);
v_value_3620_ = lean_ctor_get(v_decl_3616_, 4);
v___x_3621_ = 0;
lean_inc_ref(v_value_3620_);
v___x_3622_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3622_, 0, v_value_3620_);
v___x_3623_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3622_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3643_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3643_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3643_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3621_, v_decl_3616_, v_type_3619_, v_params_3618_, v_a_3624_, v_a_3579_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3631_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 2);
lean_ctor_set(v___x_3626_, 0, v_a_3629_);
v___x_3631_ = v___x_3626_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3629_);
v___x_3631_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3632_, 0, v_k_3617_);
v___x_3633_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3631_, v___x_3632_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
return v___x_3633_;
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_del_object(v___x_3626_);
lean_dec_ref(v_k_3617_);
v_a_3635_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3628_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3628_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3619_);
lean_dec_ref(v_params_3618_);
lean_dec_ref(v_k_3617_);
lean_dec_ref(v_decl_3616_);
return v___x_3623_;
}
}
case 4:
{
lean_object* v_cases_3644_; lean_object* v___x_3645_; 
v_cases_3644_ = lean_ctor_get(v_code_3576_, 0);
lean_inc_ref_n(v_cases_3644_, 2);
v___x_3645_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3644_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v___x_3647_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3644_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v_a_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_st_mk_ref(v___x_3648_);
v___x_3650_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3649_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v___x_3651_; lean_object* v_typeName_3652_; lean_object* v_resultType_3653_; lean_object* v_discr_3654_; lean_object* v_alts_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref_known(v___x_3650_, 1);
v___x_3651_ = lean_st_ref_get(v___x_3649_);
lean_dec(v___x_3649_);
v_typeName_3652_ = lean_ctor_get(v_cases_3644_, 0);
v_resultType_3653_ = lean_ctor_get(v_cases_3644_, 1);
v_discr_3654_ = lean_ctor_get(v_cases_3644_, 2);
v_alts_3655_ = lean_ctor_get(v_cases_3644_, 3);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_cases_3644_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3657_ = v_cases_3644_;
v_isShared_3658_ = v_isSharedCheck_3695_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_alts_3655_);
lean_inc(v_discr_3654_);
lean_inc(v_resultType_3653_);
lean_inc(v_typeName_3652_);
lean_dec(v_cases_3644_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3695_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_newArms_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_newArms_3659_ = lean_ctor_get(v___x_3651_, 1);
lean_inc_ref(v_newArms_3659_);
lean_dec(v___x_3651_);
v___x_3660_ = lean_box(2);
v___x_3661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3659_, v___x_3660_);
v___x_3662_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3655_);
v___x_3663_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3659_, v___x_3662_, v_alts_3655_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec_ref(v_newArms_3659_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3686_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3686_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3686_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___y_3669_; size_t v___x_3680_; size_t v___x_3681_; uint8_t v___x_3682_; 
v___x_3680_ = lean_ptr_addr(v_alts_3655_);
lean_dec_ref(v_alts_3655_);
v___x_3681_ = lean_ptr_addr(v_a_3664_);
v___x_3682_ = lean_usize_dec_eq(v___x_3680_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_dec_ref_known(v_code_3576_, 1);
goto v___jp_3675_;
}
else
{
size_t v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = lean_ptr_addr(v_resultType_3653_);
v___x_3684_ = lean_usize_dec_eq(v___x_3683_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_dec_ref_known(v_code_3576_, 1);
goto v___jp_3675_;
}
else
{
uint8_t v___x_3685_; 
v___x_3685_ = l_Lean_instBEqFVarId_beq(v_discr_3654_, v_discr_3654_);
if (v___x_3685_ == 0)
{
lean_dec_ref_known(v_code_3576_, 1);
goto v___jp_3675_;
}
else
{
lean_dec(v_a_3664_);
lean_del_object(v___x_3657_);
lean_dec(v_discr_3654_);
lean_dec_ref(v_resultType_3653_);
lean_dec(v_typeName_3652_);
v___y_3669_ = v_code_3576_;
goto v___jp_3668_;
}
}
}
v___jp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3670_ = lean_array_mk(v___x_3661_);
v___x_3671_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_3670_, v___y_3669_);
lean_dec_ref(v___x_3670_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3671_);
v___x_3673_ = v___x_3666_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
v___jp_3675_:
{
lean_object* v___x_3677_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 3, v_a_3664_);
v___x_3677_ = v___x_3657_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_typeName_3652_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_resultType_3653_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_discr_3654_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_a_3664_);
v___x_3677_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
v___y_3669_ = v___x_3678_;
goto v___jp_3668_;
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v___x_3661_);
lean_del_object(v___x_3657_);
lean_dec_ref(v_alts_3655_);
lean_dec(v_discr_3654_);
lean_dec_ref(v_resultType_3653_);
lean_dec(v_typeName_3652_);
lean_dec_ref_known(v_code_3576_, 1);
v_a_3687_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3663_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3663_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v___x_3649_);
lean_dec_ref_known(v_code_3576_, 1);
lean_dec_ref(v_cases_3644_);
v_a_3696_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3650_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3650_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref_known(v_code_3576_, 1);
lean_dec_ref(v_cases_3644_);
v_a_3704_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3645_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3645_);
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
default: 
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_inc(v_a_3577_);
v___x_3712_ = lean_array_mk(v_a_3577_);
v___x_3713_ = l_Array_reverse___redArg(v___x_3712_);
v___x_3714_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_3713_, v_code_3576_);
lean_dec_ref(v___x_3713_);
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
lean_dec(v_a_3721_);
lean_dec_ref(v_a_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
lean_dec(v_a_3717_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3724_, lean_object* v_i_3725_, lean_object* v_as_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3733_ = lean_array_get_size(v_as_3726_);
v___x_3734_ = lean_nat_dec_lt(v_i_3725_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
lean_dec(v_i_3725_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v_as_3726_);
return v___x_3735_;
}
else
{
lean_object* v_toCold_3736_; lean_object* v_options_3737_; lean_object* v_inheritedTraceOptions_3738_; uint8_t v_hasTrace_3739_; lean_object* v_a_3740_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; 
v_toCold_3736_ = lean_ctor_get(v___y_3730_, 0);
v_options_3737_ = lean_ctor_get(v_toCold_3736_, 2);
v_inheritedTraceOptions_3738_ = lean_ctor_get(v_toCold_3736_, 11);
v_hasTrace_3739_ = lean_ctor_get_uint8(v_options_3737_, sizeof(void*)*1);
v_a_3740_ = lean_array_fget_borrowed(v_as_3726_, v_i_3725_);
v___x_3771_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3740_);
v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3724_, v___x_3771_);
if (v_hasTrace_3739_ == 0)
{
lean_dec(v___x_3771_);
v___y_3774_ = v___y_3728_;
v___y_3775_ = v___y_3729_;
v___y_3776_ = v___y_3730_;
v___y_3777_ = v___y_3731_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3783_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3784_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3738_, v_options_3737_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_dec(v___x_3771_);
v___y_3774_ = v___y_3728_;
v___y_3775_ = v___y_3729_;
v___y_3776_ = v___y_3730_;
v___y_3777_ = v___y_3731_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3785_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3786_ = lean_unsigned_to_nat(0u);
v___x_3787_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3771_, v___x_3786_);
v___x_3788_ = l_Lean_MessageData_ofFormat(v___x_3787_);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3785_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_List_lengthTR___redArg(v___x_3772_);
v___x_3793_ = l_Nat_reprFast(v___x_3792_);
v___x_3794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
v___x_3795_ = l_Lean_MessageData_ofFormat(v___x_3794_);
v___x_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3791_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3782_, v___x_3796_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_dec_ref_known(v___x_3797_, 1);
v___y_3774_ = v___y_3728_;
v___y_3775_ = v___y_3729_;
v___y_3776_ = v___y_3730_;
v___y_3777_ = v___y_3731_;
goto v___jp_3773_;
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec(v___x_3772_);
lean_dec_ref(v_as_3726_);
lean_dec(v_i_3725_);
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
v___jp_3741_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_3742_, v___y_3747_);
lean_dec_ref(v___y_3742_);
v___x_3749_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3749_, 0, v___x_3748_);
v___x_3750_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3749_, v___y_3744_, v___y_3743_, v___y_3746_, v___y_3745_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3752_; size_t v___x_3753_; size_t v___x_3754_; uint8_t v___x_3755_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
lean_inc(v_a_3740_);
v___x_3752_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3740_, v_a_3751_);
v___x_3753_ = lean_ptr_addr(v_a_3740_);
v___x_3754_ = lean_ptr_addr(v___x_3752_);
v___x_3755_ = lean_usize_dec_eq(v___x_3753_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_unsigned_to_nat(1u);
v___x_3757_ = lean_nat_add(v_i_3725_, v___x_3756_);
v___x_3758_ = lean_array_fset(v_as_3726_, v_i_3725_, v___x_3752_);
lean_dec(v_i_3725_);
v_i_3725_ = v___x_3757_;
v_as_3726_ = v___x_3758_;
goto _start;
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec_ref(v___x_3752_);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = lean_nat_add(v_i_3725_, v___x_3760_);
lean_dec(v_i_3725_);
v_i_3725_ = v___x_3761_;
goto _start;
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec_ref(v_as_3726_);
lean_dec(v_i_3725_);
v_a_3763_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3750_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3750_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
v___jp_3773_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_array_mk(v___x_3772_);
switch(lean_obj_tag(v_a_3740_))
{
case 0:
{
lean_object* v_code_3779_; 
v_code_3779_ = lean_ctor_get(v_a_3740_, 2);
lean_inc_ref(v_code_3779_);
v___y_3742_ = v___x_3778_;
v___y_3743_ = v___y_3775_;
v___y_3744_ = v___y_3774_;
v___y_3745_ = v___y_3777_;
v___y_3746_ = v___y_3776_;
v___y_3747_ = v_code_3779_;
goto v___jp_3741_;
}
case 1:
{
lean_object* v_code_3780_; 
v_code_3780_ = lean_ctor_get(v_a_3740_, 1);
lean_inc_ref(v_code_3780_);
v___y_3742_ = v___x_3778_;
v___y_3743_ = v___y_3775_;
v___y_3744_ = v___y_3774_;
v___y_3745_ = v___y_3777_;
v___y_3746_ = v___y_3776_;
v___y_3747_ = v_code_3780_;
goto v___jp_3741_;
}
default: 
{
lean_object* v_code_3781_; 
v_code_3781_ = lean_ctor_get(v_a_3740_, 0);
lean_inc_ref(v_code_3781_);
v___y_3742_ = v___x_3778_;
v___y_3743_ = v___y_3775_;
v___y_3744_ = v___y_3774_;
v___y_3745_ = v___y_3777_;
v___y_3746_ = v___y_3776_;
v___y_3747_ = v_code_3781_;
goto v___jp_3741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3806_, lean_object* v_i_3807_, lean_object* v_as_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3806_, v_i_3807_, v_as_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___x_3806_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3816_, lean_object* v_v_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
if (lean_obj_tag(v_v_3817_) == 0)
{
lean_object* v_code_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3848_; 
v_code_3824_ = lean_ctor_get(v_v_3817_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_v_3817_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3826_ = v_v_3817_;
v_isShared_3827_ = v_isSharedCheck_3848_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_code_3824_);
lean_dec(v_v_3817_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3848_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; 
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3819_);
lean_inc(v___y_3818_);
v___x_3828_ = lean_apply_7(v_f_3816_, v_code_3824_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, lean_box(0));
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3839_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3839_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3839_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v_a_3829_);
v___x_3834_ = v___x_3826_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3836_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3834_);
v___x_3836_ = v___x_3831_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_del_object(v___x_3826_);
v_a_3840_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3828_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3828_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
else
{
lean_object* v___x_3849_; 
lean_dec_ref(v_f_3816_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v_v_3817_);
return v___x_3849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3850_, lean_object* v_v_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3850_, v_v_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3859_, lean_object* v_f_3860_, lean_object* v_v_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3860_, v_v_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3869_, lean_object* v_f_3870_, lean_object* v_v_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
uint8_t v_pu_boxed_3878_; lean_object* v_res_3879_; 
v_pu_boxed_3878_ = lean_unbox(v_pu_3869_);
v_res_3879_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_3878_, v_f_3870_, v_v_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_toSignature_3887_; lean_object* v_value_3888_; uint8_t v_recursive_3889_; lean_object* v_inlineAttr_x3f_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3916_; 
v_toSignature_3887_ = lean_ctor_get(v_decl_3881_, 0);
v_value_3888_ = lean_ctor_get(v_decl_3881_, 1);
v_recursive_3889_ = lean_ctor_get_uint8(v_decl_3881_, sizeof(void*)*3);
v_inlineAttr_x3f_3890_ = lean_ctor_get(v_decl_3881_, 2);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_decl_3881_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3892_ = v_decl_3881_;
v_isShared_3893_ = v_isSharedCheck_3916_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_inlineAttr_x3f_3890_);
lean_inc(v_value_3888_);
lean_inc(v_toSignature_3887_);
lean_dec(v_decl_3881_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3916_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_3895_ = lean_box(0);
v___x_3896_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_3894_, v_value_3888_, v___x_3895_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3907_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3907_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3907_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 1, v_a_3897_);
v___x_3902_ = v___x_3892_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_toSignature_3887_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_a_3897_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_inlineAttr_x3f_3890_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*3, v_recursive_3889_);
v___x_3902_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3902_);
v___x_3904_ = v___x_3899_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_del_object(v___x_3892_);
lean_dec(v_inlineAttr_x3f_3890_);
lean_dec_ref(v_toSignature_3887_);
v_a_3908_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3896_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3896_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_3940_, lean_object* v___f_3941_, lean_object* v_occurrence_3942_, lean_object* v_h_3943_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_3945_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3944_, v_phase_3940_, v___f_3941_, v_occurrence_3942_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_3946_, lean_object* v___f_3947_, lean_object* v_occurrence_3948_, lean_object* v_h_3949_){
_start:
{
uint8_t v_phase_boxed_3950_; lean_object* v_res_3951_; 
v_phase_boxed_3950_ = lean_unbox(v_phase_3946_);
v_res_3951_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_3950_, v___f_3947_, v_occurrence_3948_, v_h_3949_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_3953_, lean_object* v_occurrence_3954_){
_start:
{
lean_object* v___f_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; lean_object* v___x_3960_; 
v___f_3955_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_3956_ = lean_box(v_phase_3953_);
v___f_3957_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3957_, 0, v___x_3956_);
lean_closure_set(v___f_3957_, 1, v___f_3955_);
lean_closure_set(v___f_3957_, 2, v_occurrence_3954_);
v___x_3958_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_3959_ = 0;
v___x_3960_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_3958_, v_phase_3953_, v___x_3959_, v___f_3957_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_3961_, lean_object* v_occurrence_3962_){
_start:
{
uint8_t v_phase_boxed_3963_; lean_object* v_res_3964_; 
v_phase_boxed_3963_ = lean_unbox(v_phase_3961_);
v_res_3964_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_3963_, v_occurrence_3962_);
return v_res_3964_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = lean_unsigned_to_nat(3411573818u);
v___x_4017_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4018_ = l_Lean_Name_num___override(v___x_4017_, v___x_4016_);
return v___x_4018_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4021_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4022_ = l_Lean_Name_str___override(v___x_4021_, v___x_4020_);
return v___x_4022_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4025_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4026_ = l_Lean_Name_str___override(v___x_4025_, v___x_4024_);
return v___x_4026_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = lean_unsigned_to_nat(2u);
v___x_4028_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4029_ = l_Lean_Name_num___override(v___x_4028_, v___x_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4031_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4032_ = 1;
v___x_4033_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4034_ = l_Lean_registerTraceClass(v___x_4031_, v___x_4032_, v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4036_;
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
