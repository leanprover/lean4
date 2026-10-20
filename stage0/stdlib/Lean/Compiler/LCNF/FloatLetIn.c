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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_a_548_; uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_eq(v_i_542_, v_stop_543_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_array_uget_borrowed(v_as_541_, v_i_542_);
lean_inc(v___x_553_);
v___x_554_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_553_, v___x_552_, v___y_545_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; uint8_t v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = lean_unbox(v_a_555_);
if (v___x_556_ == 0)
{
lean_dec(v_a_555_);
v_a_548_ = v_b_544_;
goto v___jp_547_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = lean_unbox(v_a_555_);
lean_dec(v_a_555_);
v_a_548_ = v___x_557_;
goto v___jp_547_;
}
}
else
{
return v___x_554_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_box(v_b_544_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_stop_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
size_t v_i_boxed_566_; size_t v_stop_boxed_567_; uint8_t v_b_boxed_568_; lean_object* v_res_569_; 
v_i_boxed_566_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_567_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_b_boxed_568_ = lean_unbox(v_b_563_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_560_, v_i_boxed_566_, v_stop_boxed_567_, v_b_boxed_568_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v_as_560_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_570_, lean_object* v_args_571_, lean_object* v_val_572_, lean_object* v_a_573_, uint8_t v_b_574_, lean_object* v___y_575_){
_start:
{
uint8_t v_a_578_; uint8_t v___x_582_; 
v___x_582_ = lean_nat_dec_lt(v_a_573_, v_upperBound_570_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_a_573_);
v___x_583_ = lean_box(v_b_574_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
else
{
lean_object* v_params_585_; lean_object* v___x_586_; uint8_t v___y_588_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_params_585_ = lean_ctor_get(v_val_572_, 3);
v___x_586_ = lean_array_fget_borrowed(v_args_571_, v_a_573_);
v___x_592_ = lean_array_get_size(v_params_585_);
v___x_593_ = lean_nat_dec_lt(v_a_573_, v___x_592_);
if (v___x_593_ == 0)
{
v___y_588_ = v___x_593_;
goto v___jp_587_;
}
else
{
lean_object* v___x_594_; uint8_t v_borrow_595_; 
v___x_594_ = lean_array_fget_borrowed(v_params_585_, v_a_573_);
v_borrow_595_ = lean_ctor_get_uint8(v___x_594_, sizeof(void*)*3);
v___y_588_ = v_borrow_595_;
goto v___jp_587_;
}
v___jp_587_:
{
lean_object* v___x_589_; 
lean_inc(v___x_586_);
v___x_589_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_586_, v___y_588_, v___y_575_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; uint8_t v___x_591_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_unbox(v_a_590_);
lean_dec(v_a_590_);
if (v___x_591_ == 0)
{
v_a_578_ = v_b_574_;
goto v___jp_577_;
}
else
{
v_a_578_ = v___x_582_;
goto v___jp_577_;
}
}
else
{
lean_dec(v_a_573_);
return v___x_589_;
}
}
}
v___jp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_a_573_, v___x_579_);
lean_dec(v_a_573_);
v_a_573_ = v___x_580_;
v_b_574_ = v_a_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object* v_upperBound_596_, lean_object* v_args_597_, lean_object* v_val_598_, lean_object* v_a_599_, lean_object* v_b_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v_b_boxed_603_; lean_object* v_res_604_; 
v_b_boxed_603_ = lean_unbox(v_b_600_);
v_res_604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_596_, v_args_597_, v_val_598_, v_a_599_, v_b_boxed_603_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v_val_598_);
lean_dec_ref(v_args_597_);
lean_dec(v_upperBound_596_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object* v_as_605_, size_t v_i_606_, size_t v_stop_607_, uint8_t v_b_608_, lean_object* v___y_609_){
_start:
{
uint8_t v_a_612_; uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_eq(v_i_606_, v_stop_607_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_array_uget_borrowed(v_as_605_, v_i_606_);
lean_inc(v___x_617_);
v___x_618_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_617_, v___x_616_, v___y_609_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; uint8_t v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_unbox(v_a_619_);
if (v___x_620_ == 0)
{
lean_dec(v_a_619_);
v_a_612_ = v_b_608_;
goto v___jp_611_;
}
else
{
uint8_t v___x_621_; 
v___x_621_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
v_a_612_ = v___x_621_;
goto v___jp_611_;
}
}
else
{
return v___x_618_;
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(v_b_608_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
v___jp_611_:
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_606_, v___x_613_);
v_i_606_ = v___x_614_;
v_b_608_ = v_a_612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_624_, lean_object* v_i_625_, lean_object* v_stop_626_, lean_object* v_b_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
size_t v_i_boxed_630_; size_t v_stop_boxed_631_; uint8_t v_b_boxed_632_; lean_object* v_res_633_; 
v_i_boxed_630_ = lean_unbox_usize(v_i_625_);
lean_dec(v_i_625_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_626_);
lean_dec(v_stop_626_);
v_b_boxed_632_ = lean_unbox(v_b_627_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_624_, v_i_boxed_630_, v_stop_boxed_631_, v_b_boxed_632_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v_as_624_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object* v_value_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
switch(lean_obj_tag(v_value_634_))
{
case 2:
{
lean_object* v_struct_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v_struct_641_ = lean_ctor_get(v_value_634_, 2);
lean_inc(v_struct_641_);
lean_dec_ref_known(v_value_634_, 3);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_struct_641_);
v___x_643_ = 1;
v___x_644_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_642_, v___x_643_, v_a_635_);
return v___x_644_;
}
case 3:
{
lean_object* v_declName_645_; lean_object* v_args_646_; lean_object* v___x_647_; 
v_declName_645_ = lean_ctor_get(v_value_634_, 0);
lean_inc(v_declName_645_);
v_args_646_ = lean_ctor_get(v_value_634_, 2);
lean_inc_ref(v_args_646_);
lean_dec_ref_known(v_value_634_, 3);
v___x_647_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_645_, v_a_639_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_668_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_668_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_668_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_668_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
if (lean_obj_tag(v_a_648_) == 0)
{
uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_652_ = 0;
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_array_get_size(v_args_646_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_dec_ref(v_args_646_);
v___x_656_ = lean_box(v___x_652_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_656_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
lean_del_object(v___x_650_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_654_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_646_, v___x_660_, v___x_661_, v___x_652_, v_a_635_);
lean_dec_ref(v_args_646_);
return v___x_662_;
}
}
else
{
lean_object* v_val_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
lean_del_object(v___x_650_);
v_val_663_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_a_648_, 1);
v___x_664_ = lean_array_get_size(v_args_646_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = 0;
v___x_667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_664_, v_args_646_, v_val_663_, v___x_665_, v___x_666_, v_a_635_);
lean_dec(v_val_663_);
lean_dec_ref(v_args_646_);
return v___x_667_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_args_646_);
v_a_669_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_647_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_647_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_677_; lean_object* v_args_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_fvarId_677_ = lean_ctor_get(v_value_634_, 0);
lean_inc(v_fvarId_677_);
v_args_678_ = lean_ctor_get(v_value_634_, 1);
lean_inc_ref(v_args_678_);
lean_dec_ref_known(v_value_634_, 2);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v_fvarId_677_);
v___x_680_ = 0;
v___x_681_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_679_, v___x_680_, v_a_635_);
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_array_get_size(v_args_678_);
v___x_685_ = lean_nat_dec_lt(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_dec_ref(v_args_678_);
return v___x_681_;
}
else
{
size_t v___x_686_; size_t v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; 
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = lean_usize_of_nat(v___x_684_);
v___x_688_ = lean_unbox(v_a_682_);
lean_dec(v_a_682_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_678_, v___x_686_, v___x_687_, v___x_688_, v_a_635_);
lean_dec_ref(v_args_678_);
return v___x_689_;
}
}
default: 
{
uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_value_634_);
v___x_690_ = 0;
v___x_691_ = lean_box(v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(lean_object* v_value_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object* v_env_701_, lean_object* v_value_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object* v_env_710_, lean_object* v_value_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_710_, v_value_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_env_710_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object* v_as_719_, size_t v_i_720_, size_t v_stop_721_, uint8_t v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_719_, v_i_720_, v_stop_721_, v_b_722_, v___y_723_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object* v_as_730_, lean_object* v_i_731_, lean_object* v_stop_732_, lean_object* v_b_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
size_t v_i_boxed_740_; size_t v_stop_boxed_741_; uint8_t v_b_boxed_742_; lean_object* v_res_743_; 
v_i_boxed_740_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_stop_boxed_741_ = lean_unbox_usize(v_stop_732_);
lean_dec(v_stop_732_);
v_b_boxed_742_ = lean_unbox(v_b_733_);
v_res_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_730_, v_i_boxed_740_, v_stop_boxed_741_, v_b_boxed_742_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v_as_730_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object* v_upperBound_744_, lean_object* v_args_745_, lean_object* v_val_746_, lean_object* v_inst_747_, lean_object* v_R_748_, lean_object* v_a_749_, uint8_t v_b_750_, lean_object* v_c_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_744_, v_args_745_, v_val_746_, v_a_749_, v_b_750_, v___y_752_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object* v_upperBound_759_, lean_object* v_args_760_, lean_object* v_val_761_, lean_object* v_inst_762_, lean_object* v_R_763_, lean_object* v_a_764_, lean_object* v_b_765_, lean_object* v_c_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_b_boxed_773_; lean_object* v_res_774_; 
v_b_boxed_773_ = lean_unbox(v_b_765_);
v_res_774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_759_, v_args_760_, v_val_761_, v_inst_762_, v_R_763_, v_a_764_, v_b_boxed_773_, v_c_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v_val_761_);
lean_dec_ref(v_args_760_);
lean_dec(v_upperBound_759_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object* v_as_775_, size_t v_i_776_, size_t v_stop_777_, uint8_t v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_775_, v_i_776_, v_stop_777_, v_b_778_, v___y_779_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object* v_as_786_, lean_object* v_i_787_, lean_object* v_stop_788_, lean_object* v_b_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
size_t v_i_boxed_796_; size_t v_stop_boxed_797_; uint8_t v_b_boxed_798_; lean_object* v_res_799_; 
v_i_boxed_796_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_stop_boxed_797_ = lean_unbox_usize(v_stop_788_);
lean_dec(v_stop_788_);
v_b_boxed_798_ = lean_unbox(v_b_789_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_786_, v_i_boxed_796_, v_stop_boxed_797_, v_b_boxed_798_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v_as_786_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object* v_value_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
if (lean_obj_tag(v_value_800_) == 0)
{
lean_object* v_decl_807_; lean_object* v_value_808_; lean_object* v___x_809_; 
v_decl_807_ = lean_ctor_get(v_value_800_, 0);
lean_inc_ref(v_decl_807_);
lean_dec_ref_known(v_value_800_, 1);
v_value_808_ = lean_ctor_get(v_decl_807_, 3);
lean_inc(v_value_808_);
lean_dec_ref(v_decl_807_);
v___x_809_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_808_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_809_;
}
else
{
uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_value_800_);
v___x_810_ = 0;
v___x_811_ = lean_box(v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object* v_value_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object* v_env_821_, lean_object* v_value_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object* v_env_830_, lean_object* v_value_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_830_, v_value_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_env_830_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(lean_object* v_a_839_, lean_object* v_b_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
lean_dec(v_b_840_);
lean_dec(v_a_839_);
return v_x_841_;
}
else
{
lean_object* v_key_842_; lean_object* v_value_843_; lean_object* v_tail_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_856_; 
v_key_842_ = lean_ctor_get(v_x_841_, 0);
v_value_843_ = lean_ctor_get(v_x_841_, 1);
v_tail_844_ = lean_ctor_get(v_x_841_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_841_);
if (v_isSharedCheck_856_ == 0)
{
v___x_846_ = v_x_841_;
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_tail_844_);
lean_inc(v_value_843_);
lean_inc(v_key_842_);
lean_dec(v_x_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_instBEqFVarId_beq(v_key_842_, v_a_839_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_839_, v_b_840_, v_tail_844_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 2, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_key_842_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_value_843_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v___x_854_; 
lean_dec(v_value_843_);
lean_dec(v_key_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_b_840_);
lean_ctor_set(v___x_846_, 0, v_a_839_);
v___x_854_ = v___x_846_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_839_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_b_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_tail_844_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(lean_object* v_m_857_, lean_object* v_a_858_, lean_object* v_b_859_){
_start:
{
lean_object* v_size_860_; lean_object* v_buckets_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_904_; 
v_size_860_ = lean_ctor_get(v_m_857_, 0);
v_buckets_861_ = lean_ctor_get(v_m_857_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_m_857_);
if (v_isSharedCheck_904_ == 0)
{
v___x_863_ = v_m_857_;
v_isShared_864_ = v_isSharedCheck_904_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_buckets_861_);
lean_inc(v_size_860_);
lean_dec(v_m_857_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_904_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v_fold_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v_bkt_878_; uint8_t v___x_879_; 
v___x_865_ = lean_array_get_size(v_buckets_861_);
v___x_866_ = l_Lean_instHashableFVarId_hash(v_a_858_);
v___x_867_ = 32ULL;
v___x_868_ = lean_uint64_shift_right(v___x_866_, v___x_867_);
v_fold_869_ = lean_uint64_xor(v___x_866_, v___x_868_);
v___x_870_ = 16ULL;
v___x_871_ = lean_uint64_shift_right(v_fold_869_, v___x_870_);
v___x_872_ = lean_uint64_xor(v_fold_869_, v___x_871_);
v___x_873_ = lean_uint64_to_usize(v___x_872_);
v___x_874_ = lean_usize_of_nat(v___x_865_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_sub(v___x_874_, v___x_875_);
v___x_877_ = lean_usize_land(v___x_873_, v___x_876_);
v_bkt_878_ = lean_array_uget_borrowed(v_buckets_861_, v___x_877_);
v___x_879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_858_, v_bkt_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v_size_x27_881_; lean_object* v___x_882_; lean_object* v_buckets_x27_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v_size_x27_881_ = lean_nat_add(v_size_860_, v___x_880_);
lean_dec(v_size_860_);
lean_inc(v_bkt_878_);
v___x_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_882_, 0, v_a_858_);
lean_ctor_set(v___x_882_, 1, v_b_859_);
lean_ctor_set(v___x_882_, 2, v_bkt_878_);
v_buckets_x27_883_ = lean_array_uset(v_buckets_861_, v___x_877_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(4u);
v___x_885_ = lean_nat_mul(v_size_x27_881_, v___x_884_);
v___x_886_ = lean_unsigned_to_nat(3u);
v___x_887_ = lean_nat_div(v___x_885_, v___x_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_array_get_size(v_buckets_x27_883_);
v___x_889_ = lean_nat_dec_le(v___x_887_, v___x_888_);
lean_dec(v___x_887_);
if (v___x_889_ == 0)
{
lean_object* v_val_890_; lean_object* v___x_892_; 
v_val_890_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_883_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_val_890_);
lean_ctor_set(v___x_863_, 0, v_size_x27_881_);
v___x_892_ = v___x_863_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_size_x27_881_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_val_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_895_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_buckets_x27_883_);
lean_ctor_set(v___x_863_, 0, v_size_x27_881_);
v___x_895_ = v___x_863_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_size_x27_881_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_buckets_x27_883_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v___x_897_; lean_object* v_buckets_x27_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
lean_inc(v_bkt_878_);
v___x_897_ = lean_box(0);
v_buckets_x27_898_ = lean_array_uset(v_buckets_861_, v___x_877_, v___x_897_);
v___x_899_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_858_, v_b_859_, v_bkt_878_);
v___x_900_ = lean_array_uset(v_buckets_x27_898_, v___x_877_, v___x_899_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_900_);
v___x_902_ = v___x_863_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_size_860_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(lean_object* v_a_905_, lean_object* v_x_906_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_box(0);
return v___x_907_;
}
else
{
lean_object* v_key_908_; lean_object* v_value_909_; lean_object* v_tail_910_; uint8_t v___x_911_; 
v_key_908_ = lean_ctor_get(v_x_906_, 0);
v_value_909_ = lean_ctor_get(v_x_906_, 1);
v_tail_910_ = lean_ctor_get(v_x_906_, 2);
v___x_911_ = l_Lean_instBEqFVarId_beq(v_key_908_, v_a_905_);
if (v___x_911_ == 0)
{
v_x_906_ = v_tail_910_;
goto _start;
}
else
{
lean_object* v___x_913_; 
lean_inc(v_value_909_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v_value_909_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_914_, lean_object* v_x_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_914_, v_x_915_);
lean_dec(v_x_915_);
lean_dec(v_a_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object* v_m_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_buckets_919_; lean_object* v___x_920_; uint64_t v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; uint64_t v_fold_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v___x_927_; size_t v___x_928_; size_t v___x_929_; size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_buckets_919_ = lean_ctor_get(v_m_917_, 1);
v___x_920_ = lean_array_get_size(v_buckets_919_);
v___x_921_ = l_Lean_instHashableFVarId_hash(v_a_918_);
v___x_922_ = 32ULL;
v___x_923_ = lean_uint64_shift_right(v___x_921_, v___x_922_);
v_fold_924_ = lean_uint64_xor(v___x_921_, v___x_923_);
v___x_925_ = 16ULL;
v___x_926_ = lean_uint64_shift_right(v_fold_924_, v___x_925_);
v___x_927_ = lean_uint64_xor(v_fold_924_, v___x_926_);
v___x_928_ = lean_uint64_to_usize(v___x_927_);
v___x_929_ = lean_usize_of_nat(v___x_920_);
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_sub(v___x_929_, v___x_930_);
v___x_932_ = lean_usize_land(v___x_928_, v___x_931_);
v___x_933_ = lean_array_uget_borrowed(v_buckets_919_, v___x_932_);
v___x_934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_918_, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object* v_m_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_m_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* v_plannedDecision_938_, lean_object* v_var_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_st_ref_get(v_a_940_);
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_942_, v_var_939_);
lean_dec(v___x_942_);
if (lean_obj_tag(v___x_943_) == 1)
{
lean_object* v_val_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_968_; 
v_val_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_968_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_val_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
if (lean_obj_tag(v_val_944_) == 3)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_948_ = lean_st_ref_take(v_a_940_);
v___x_949_ = lean_box(0);
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_948_, v_var_939_, v_plannedDecision_938_);
v___x_951_ = lean_st_ref_put(v_a_940_, v___x_950_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 0);
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_953_ = v___x_946_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_949_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_944_, v_plannedDecision_938_);
lean_dec(v_plannedDecision_938_);
lean_dec(v_val_944_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_956_ = lean_st_ref_take(v_a_940_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_box(2);
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_956_, v_var_939_, v___x_958_);
v___x_960_ = lean_st_ref_put(v_a_940_, v___x_959_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 0);
lean_ctor_set(v___x_946_, 0, v___x_957_);
v___x_962_ = v___x_946_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_var_939_);
v___x_964_ = lean_box(0);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 0);
lean_ctor_set(v___x_946_, 0, v___x_964_);
v___x_966_ = v___x_946_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v___x_943_);
lean_dec(v_var_939_);
lean_dec(v_plannedDecision_938_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_971_, lean_object* v_var_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_971_, v_var_972_, v_a_973_);
lean_dec(v_a_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_976_, lean_object* v_var_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_976_, v_var_977_, v_a_978_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_986_, lean_object* v_var_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_986_, v_var_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec(v_a_988_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_996_, lean_object* v_m_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_997_, v_a_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1000_, lean_object* v_m_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1000_, v_m_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_m_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object* v_00_u03b2_1004_, lean_object* v_m_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_1005_, v_a_1006_, v_b_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object* v_00_u03b2_1009_, lean_object* v_a_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1013_, lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_1013_, v_a_1014_, v_x_1015_);
lean_dec(v_x_1015_);
lean_dec(v_a_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object* v_00_u03b2_1017_, lean_object* v_a_1018_, lean_object* v_b_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_1018_, v_b_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1022_, lean_object* v_f_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
switch(lean_obj_tag(v_alt_1022_))
{
case 0:
{
lean_object* v_code_1031_; lean_object* v___x_1032_; 
v_code_1031_ = lean_ctor_get(v_alt_1022_, 2);
lean_inc_ref(v_code_1031_);
lean_dec_ref_known(v_alt_1022_, 3);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc(v___y_1024_);
v___x_1032_ = lean_apply_8(v_f_1023_, v_code_1031_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
return v___x_1032_;
}
case 1:
{
lean_object* v_code_1033_; lean_object* v___x_1034_; 
v_code_1033_ = lean_ctor_get(v_alt_1022_, 1);
lean_inc_ref(v_code_1033_);
lean_dec_ref_known(v_alt_1022_, 2);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc(v___y_1024_);
v___x_1034_ = lean_apply_8(v_f_1023_, v_code_1033_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
return v___x_1034_;
}
default: 
{
lean_object* v_code_1035_; lean_object* v___x_1036_; 
v_code_1035_ = lean_ctor_get(v_alt_1022_, 0);
lean_inc_ref(v_code_1035_);
lean_dec_ref_known(v_alt_1022_, 1);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc(v___y_1024_);
v___x_1036_ = lean_apply_8(v_f_1023_, v_code_1035_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1037_, lean_object* v_f_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1037_, v_f_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
return v_res_1046_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_instMonadEIO___redArg();
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_toApplicative_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1125_; 
v___x_1060_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1061_ = l_StateRefT_x27_instMonad___redArg(v___x_1060_);
v_toApplicative_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1061_, 1);
lean_dec(v_unused_1126_);
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1125_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_toApplicative_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1125_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_toFunctor_1066_; lean_object* v_toSeq_1067_; lean_object* v_toSeqLeft_1068_; lean_object* v_toSeqRight_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1123_; 
v_toFunctor_1066_ = lean_ctor_get(v_toApplicative_1062_, 0);
v_toSeq_1067_ = lean_ctor_get(v_toApplicative_1062_, 2);
v_toSeqLeft_1068_ = lean_ctor_get(v_toApplicative_1062_, 3);
v_toSeqRight_1069_ = lean_ctor_get(v_toApplicative_1062_, 4);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_toApplicative_1062_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_toApplicative_1062_, 1);
lean_dec(v_unused_1124_);
v___x_1071_ = v_toApplicative_1062_;
v_isShared_1072_ = v_isSharedCheck_1123_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_toSeqRight_1069_);
lean_inc(v_toSeqLeft_1068_);
lean_inc(v_toSeq_1067_);
lean_inc(v_toFunctor_1066_);
lean_dec(v_toApplicative_1062_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1123_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___f_1078_; lean_object* v___f_1079_; lean_object* v___f_1080_; lean_object* v___x_1082_; 
v___f_1073_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1074_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1066_);
v___f_1075_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1075_, 0, v_toFunctor_1066_);
v___f_1076_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1076_, 0, v_toFunctor_1066_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___f_1075_);
lean_ctor_set(v___x_1077_, 1, v___f_1076_);
v___f_1078_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1078_, 0, v_toSeqRight_1069_);
v___f_1079_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1079_, 0, v_toSeqLeft_1068_);
v___f_1080_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1080_, 0, v_toSeq_1067_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___f_1078_);
lean_ctor_set(v___x_1071_, 3, v___f_1079_);
lean_ctor_set(v___x_1071_, 2, v___f_1080_);
lean_ctor_set(v___x_1071_, 1, v___f_1073_);
lean_ctor_set(v___x_1071_, 0, v___x_1077_);
v___x_1082_ = v___x_1071_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___f_1073_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v___f_1080_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v___f_1079_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v___f_1078_);
v___x_1082_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v___f_1074_);
lean_ctor_set(v___x_1064_, 0, v___x_1082_);
v___x_1084_ = v___x_1064_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___f_1074_);
v___x_1084_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v_toApplicative_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1119_; 
v___x_1085_ = l_StateRefT_x27_instMonad___redArg(v___x_1084_);
v_toApplicative_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v___x_1085_, 1);
lean_dec(v_unused_1120_);
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1119_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_toApplicative_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1119_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_toFunctor_1090_; lean_object* v_toSeq_1091_; lean_object* v_toSeqLeft_1092_; lean_object* v_toSeqRight_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1117_; 
v_toFunctor_1090_ = lean_ctor_get(v_toApplicative_1086_, 0);
v_toSeq_1091_ = lean_ctor_get(v_toApplicative_1086_, 2);
v_toSeqLeft_1092_ = lean_ctor_get(v_toApplicative_1086_, 3);
v_toSeqRight_1093_ = lean_ctor_get(v_toApplicative_1086_, 4);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_toApplicative_1086_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_toApplicative_1086_, 1);
lean_dec(v_unused_1118_);
v___x_1095_ = v_toApplicative_1086_;
v_isShared_1096_ = v_isSharedCheck_1117_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_toSeqRight_1093_);
lean_inc(v_toSeqLeft_1092_);
lean_inc(v_toSeq_1091_);
lean_inc(v_toFunctor_1090_);
lean_dec(v_toApplicative_1086_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1117_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1106_; 
v___f_1097_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1098_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1090_);
v___f_1099_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1099_, 0, v_toFunctor_1090_);
v___f_1100_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1100_, 0, v_toFunctor_1090_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___f_1099_);
lean_ctor_set(v___x_1101_, 1, v___f_1100_);
v___f_1102_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1102_, 0, v_toSeqRight_1093_);
v___f_1103_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1103_, 0, v_toSeqLeft_1092_);
v___f_1104_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1104_, 0, v_toSeq_1091_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 4, v___f_1102_);
lean_ctor_set(v___x_1095_, 3, v___f_1103_);
lean_ctor_set(v___x_1095_, 2, v___f_1104_);
lean_ctor_set(v___x_1095_, 1, v___f_1097_);
lean_ctor_set(v___x_1095_, 0, v___x_1101_);
v___x_1106_ = v___x_1095_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___f_1097_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v___f_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v___f_1103_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v___f_1102_);
v___x_1106_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___f_1098_);
lean_ctor_set(v___x_1088_, 0, v___x_1106_);
v___x_1108_ = v___x_1088_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___f_1098_);
v___x_1108_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_8045__overap_1113_; lean_object* v___x_1114_; 
v___x_1109_ = l_ReaderT_instMonad___redArg(v___x_1108_);
v___x_1110_ = l_StateRefT_x27_instMonad___redArg(v___x_1109_);
v___x_1111_ = lean_box(0);
v___x_1112_ = l_instInhabitedOfMonad___redArg(v___x_1110_, v___x_1111_);
v___x_8045__overap_1113_ = lean_panic_fn_borrowed(v___x_1112_, v_msg_1052_);
lean_dec(v___x_1112_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v___y_1054_);
lean_inc(v___y_1053_);
v___x_1114_ = lean_apply_7(v___x_8045__overap_1113_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, lean_box(0));
return v___x_1114_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec(v___y_1128_);
return v_res_1135_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1140_ = lean_unsigned_to_nat(40u);
v___x_1141_ = lean_unsigned_to_nat(49u);
v___x_1142_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1143_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1144_ = l_mkPanicMessageWithDecl(v___x_1143_, v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1145_, lean_object* v_e_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_ty_1155_; lean_object* v_body_1156_; uint8_t v___x_1159_; 
v___x_1159_ = l_Lean_Expr_hasFVar(v_e_1146_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec_ref(v_e_1146_);
lean_dec_ref(v_f_1145_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
else
{
switch(lean_obj_tag(v_e_1146_))
{
case 1:
{
lean_object* v_fvarId_1162_; lean_object* v___x_1163_; 
v_fvarId_1162_ = lean_ctor_get(v_e_1146_, 0);
lean_inc(v_fvarId_1162_);
lean_dec_ref_known(v_e_1146_, 1);
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
lean_inc(v___y_1150_);
lean_inc_ref(v___y_1149_);
lean_inc(v___y_1148_);
lean_inc(v___y_1147_);
v___x_1163_ = lean_apply_8(v_f_1145_, v_fvarId_1162_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, lean_box(0));
return v___x_1163_;
}
case 2:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref_known(v_e_1146_, 1);
lean_dec_ref(v_f_1145_);
v___x_1164_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1165_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1164_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1165_;
}
case 5:
{
lean_object* v_fn_1166_; lean_object* v_arg_1167_; lean_object* v___x_1168_; 
v_fn_1166_ = lean_ctor_get(v_e_1146_, 0);
lean_inc_ref(v_fn_1166_);
v_arg_1167_ = lean_ctor_get(v_e_1146_, 1);
lean_inc_ref(v_arg_1167_);
lean_dec_ref_known(v_e_1146_, 2);
lean_inc_ref(v_f_1145_);
v___x_1168_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1145_, v_fn_1166_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_dec_ref_known(v___x_1168_, 1);
v_e_1146_ = v_arg_1167_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1167_);
lean_dec_ref(v_f_1145_);
return v___x_1168_;
}
}
case 6:
{
lean_object* v_binderType_1170_; lean_object* v_body_1171_; 
v_binderType_1170_ = lean_ctor_get(v_e_1146_, 1);
lean_inc_ref(v_binderType_1170_);
v_body_1171_ = lean_ctor_get(v_e_1146_, 2);
lean_inc_ref(v_body_1171_);
lean_dec_ref_known(v_e_1146_, 3);
v_ty_1155_ = v_binderType_1170_;
v_body_1156_ = v_body_1171_;
goto v___jp_1154_;
}
case 7:
{
lean_object* v_binderType_1172_; lean_object* v_body_1173_; 
v_binderType_1172_ = lean_ctor_get(v_e_1146_, 1);
lean_inc_ref(v_binderType_1172_);
v_body_1173_ = lean_ctor_get(v_e_1146_, 2);
lean_inc_ref(v_body_1173_);
lean_dec_ref_known(v_e_1146_, 3);
v_ty_1155_ = v_binderType_1172_;
v_body_1156_ = v_body_1173_;
goto v___jp_1154_;
}
case 8:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref_known(v_e_1146_, 4);
lean_dec_ref(v_f_1145_);
v___x_1174_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1175_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1174_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1175_;
}
case 11:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref_known(v_e_1146_, 3);
lean_dec_ref(v_f_1145_);
v___x_1176_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1177_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1176_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1177_;
}
default: 
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_e_1146_);
lean_dec_ref(v_f_1145_);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
v___jp_1154_:
{
lean_object* v___x_1157_; 
lean_inc_ref(v_f_1145_);
v___x_1157_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1145_, v_ty_1155_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_dec_ref_known(v___x_1157_, 1);
v_e_1146_ = v_body_1156_;
goto _start;
}
else
{
lean_dec_ref(v_body_1156_);
lean_dec_ref(v_f_1145_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1180_, lean_object* v_e_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1180_, v_e_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1190_, lean_object* v_param_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_type_1199_; lean_object* v___x_1200_; 
v_type_1199_ = lean_ctor_get(v_param_1191_, 2);
lean_inc_ref(v_type_1199_);
lean_dec_ref(v_param_1191_);
v___x_1200_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1190_, v_type_1199_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1201_, lean_object* v_param_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1201_, v_param_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1203_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1211_, lean_object* v_f_1212_, lean_object* v_as_1213_, size_t v_i_1214_, size_t v_stop_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_usize_dec_eq(v_i_1214_, v_stop_1215_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_array_uget_borrowed(v_as_1213_, v_i_1214_);
lean_inc(v___x_1225_);
lean_inc_ref(v_f_1212_);
v___x_1226_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1212_, v___x_1225_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; size_t v___x_1228_; size_t v___x_1229_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1214_, v___x_1228_);
v_i_1214_ = v___x_1229_;
v_b_1216_ = v_a_1227_;
goto _start;
}
else
{
lean_dec_ref(v_f_1212_);
return v___x_1226_;
}
}
else
{
lean_object* v___x_1231_; 
lean_dec_ref(v_f_1212_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_b_1216_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1232_, lean_object* v_f_1233_, lean_object* v_as_1234_, lean_object* v_i_1235_, lean_object* v_stop_1236_, lean_object* v_b_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v_pu_boxed_1245_; size_t v_i_boxed_1246_; size_t v_stop_boxed_1247_; lean_object* v_res_1248_; 
v_pu_boxed_1245_ = lean_unbox(v_pu_1232_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_stop_boxed_1247_ = lean_unbox_usize(v_stop_1236_);
lean_dec(v_stop_1236_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1245_, v_f_1233_, v_as_1234_, v_i_boxed_1246_, v_stop_boxed_1247_, v_b_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v_as_1234_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1249_, lean_object* v_arg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
switch(lean_obj_tag(v_arg_1250_))
{
case 0:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_f_1249_);
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
case 1:
{
lean_object* v_fvarId_1260_; lean_object* v___x_1261_; 
v_fvarId_1260_ = lean_ctor_get(v_arg_1250_, 0);
lean_inc(v_fvarId_1260_);
lean_dec_ref_known(v_arg_1250_, 1);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1255_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc(v___y_1251_);
v___x_1261_ = lean_apply_8(v_f_1249_, v_fvarId_1260_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, lean_box(0));
return v___x_1261_;
}
default: 
{
lean_object* v_expr_1262_; lean_object* v___x_1263_; 
v_expr_1262_ = lean_ctor_get(v_arg_1250_, 0);
lean_inc_ref(v_expr_1262_);
lean_dec_ref_known(v_arg_1250_, 1);
v___x_1263_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1249_, v_expr_1262_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1264_, lean_object* v_arg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1264_, v_arg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1274_, lean_object* v_f_1275_, lean_object* v_as_1276_, size_t v_i_1277_, size_t v_stop_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_usize_dec_eq(v_i_1277_, v_stop_1278_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_array_uget_borrowed(v_as_1276_, v_i_1277_);
lean_inc(v___x_1288_);
lean_inc_ref(v_f_1275_);
v___x_1289_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1275_, v___x_1288_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; size_t v___x_1291_; size_t v___x_1292_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1277_, v___x_1291_);
v_i_1277_ = v___x_1292_;
v_b_1279_ = v_a_1290_;
goto _start;
}
else
{
lean_dec_ref(v_f_1275_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1294_; 
lean_dec_ref(v_f_1275_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_b_1279_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1295_, lean_object* v_f_1296_, lean_object* v_as_1297_, lean_object* v_i_1298_, lean_object* v_stop_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v_pu_boxed_1308_; size_t v_i_boxed_1309_; size_t v_stop_boxed_1310_; lean_object* v_res_1311_; 
v_pu_boxed_1308_ = lean_unbox(v_pu_1295_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1298_);
lean_dec(v_i_1298_);
v_stop_boxed_1310_ = lean_unbox_usize(v_stop_1299_);
lean_dec(v_stop_1299_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1308_, v_f_1296_, v_as_1297_, v_i_boxed_1309_, v_stop_boxed_1310_, v_b_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v_as_1297_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1312_, lean_object* v_f_1313_, lean_object* v_e_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_args_1323_; 
switch(lean_obj_tag(v_e_1314_))
{
case 2:
{
lean_object* v_struct_1332_; lean_object* v___x_1333_; 
v_struct_1332_ = lean_ctor_get(v_e_1314_, 2);
lean_inc(v_struct_1332_);
lean_dec_ref_known(v_e_1314_, 3);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1333_ = lean_apply_8(v_f_1313_, v_struct_1332_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1333_;
}
case 3:
{
lean_object* v_args_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_args_1334_ = lean_ctor_get(v_e_1314_, 2);
lean_inc_ref(v_args_1334_);
lean_dec_ref_known(v_e_1314_, 3);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_array_get_size(v_args_1334_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_nat_dec_lt(v___x_1335_, v___x_1336_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_args_1334_);
lean_dec_ref(v_f_1313_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
return v___x_1339_;
}
else
{
size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = lean_usize_of_nat(v___x_1336_);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1312_, v_f_1313_, v_args_1334_, v___x_1340_, v___x_1341_, v___x_1337_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v_args_1334_);
return v___x_1342_;
}
}
case 4:
{
lean_object* v_fvarId_1343_; lean_object* v_args_1344_; lean_object* v___x_1345_; 
v_fvarId_1343_ = lean_ctor_get(v_e_1314_, 0);
lean_inc(v_fvarId_1343_);
v_args_1344_ = lean_ctor_get(v_e_1314_, 1);
lean_inc_ref(v_args_1344_);
lean_dec_ref_known(v_e_1314_, 2);
lean_inc_ref(v_f_1313_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1345_ = lean_apply_8(v_f_1313_, v_fvarId_1343_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1359_; 
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1345_, 0);
lean_dec(v_unused_1360_);
v___x_1347_ = v___x_1345_;
v_isShared_1348_ = v_isSharedCheck_1359_;
goto v_resetjp_1346_;
}
else
{
lean_dec(v___x_1345_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1359_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_array_get_size(v_args_1344_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref(v_args_1344_);
lean_dec_ref(v_f_1313_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1354_ = v___x_1347_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1351_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
lean_del_object(v___x_1347_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_of_nat(v___x_1350_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1312_, v_f_1313_, v_args_1344_, v___x_1356_, v___x_1357_, v___x_1351_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v_args_1344_);
return v___x_1358_;
}
}
}
else
{
lean_dec_ref(v_args_1344_);
lean_dec_ref(v_f_1313_);
return v___x_1345_;
}
}
case 5:
{
lean_object* v_args_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_args_1361_ = lean_ctor_get(v_e_1314_, 1);
lean_inc_ref(v_args_1361_);
lean_dec_ref_known(v_e_1314_, 2);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_array_get_size(v_args_1361_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v_args_1361_);
lean_dec_ref(v_f_1313_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
return v___x_1366_;
}
else
{
size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = lean_usize_of_nat(v___x_1363_);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1312_, v_f_1313_, v_args_1361_, v___x_1367_, v___x_1368_, v___x_1364_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v_args_1361_);
return v___x_1369_;
}
}
case 6:
{
lean_object* v_var_1370_; lean_object* v___x_1371_; 
v_var_1370_ = lean_ctor_get(v_e_1314_, 1);
lean_inc(v_var_1370_);
lean_dec_ref_known(v_e_1314_, 2);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1371_ = lean_apply_8(v_f_1313_, v_var_1370_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1371_;
}
case 7:
{
lean_object* v_var_1372_; lean_object* v___x_1373_; 
v_var_1372_ = lean_ctor_get(v_e_1314_, 1);
lean_inc(v_var_1372_);
lean_dec_ref_known(v_e_1314_, 2);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1373_ = lean_apply_8(v_f_1313_, v_var_1372_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1373_;
}
case 8:
{
lean_object* v_var_1374_; lean_object* v___x_1375_; 
v_var_1374_ = lean_ctor_get(v_e_1314_, 2);
lean_inc(v_var_1374_);
lean_dec_ref_known(v_e_1314_, 3);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1375_ = lean_apply_8(v_f_1313_, v_var_1374_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1375_;
}
case 9:
{
lean_object* v_args_1376_; 
v_args_1376_ = lean_ctor_get(v_e_1314_, 1);
lean_inc_ref(v_args_1376_);
lean_dec_ref_known(v_e_1314_, 2);
v_args_1323_ = v_args_1376_;
goto v___jp_1322_;
}
case 10:
{
lean_object* v_args_1377_; 
v_args_1377_ = lean_ctor_get(v_e_1314_, 1);
lean_inc_ref(v_args_1377_);
lean_dec_ref_known(v_e_1314_, 2);
v_args_1323_ = v_args_1377_;
goto v___jp_1322_;
}
case 11:
{
lean_object* v_var_1378_; lean_object* v___x_1379_; 
v_var_1378_ = lean_ctor_get(v_e_1314_, 1);
lean_inc(v_var_1378_);
lean_dec_ref_known(v_e_1314_, 2);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1379_ = lean_apply_8(v_f_1313_, v_var_1378_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1379_;
}
case 12:
{
lean_object* v_var_1380_; lean_object* v_args_1381_; lean_object* v___x_1382_; 
v_var_1380_ = lean_ctor_get(v_e_1314_, 0);
lean_inc(v_var_1380_);
v_args_1381_ = lean_ctor_get(v_e_1314_, 2);
lean_inc_ref(v_args_1381_);
lean_dec_ref_known(v_e_1314_, 3);
lean_inc_ref(v_f_1313_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1382_ = lean_apply_8(v_f_1313_, v_var_1380_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___x_1382_, 0);
lean_dec(v_unused_1397_);
v___x_1384_ = v___x_1382_;
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v___x_1382_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_array_get_size(v_args_1381_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_nat_dec_lt(v___x_1386_, v___x_1387_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref(v_args_1381_);
lean_dec_ref(v_f_1313_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1391_ = v___x_1384_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1388_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
lean_del_object(v___x_1384_);
v___x_1393_ = ((size_t)0ULL);
v___x_1394_ = lean_usize_of_nat(v___x_1387_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1312_, v_f_1313_, v_args_1381_, v___x_1393_, v___x_1394_, v___x_1388_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v_args_1381_);
return v___x_1395_;
}
}
}
else
{
lean_dec_ref(v_args_1381_);
lean_dec_ref(v_f_1313_);
return v___x_1382_;
}
}
case 13:
{
lean_object* v_fvarId_1398_; lean_object* v___x_1399_; 
v_fvarId_1398_ = lean_ctor_get(v_e_1314_, 1);
lean_inc(v_fvarId_1398_);
lean_dec_ref_known(v_e_1314_, 2);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1399_ = lean_apply_8(v_f_1313_, v_fvarId_1398_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1399_;
}
case 14:
{
lean_object* v_fvarId_1400_; lean_object* v___x_1401_; 
v_fvarId_1400_ = lean_ctor_get(v_e_1314_, 0);
lean_inc(v_fvarId_1400_);
lean_dec_ref_known(v_e_1314_, 1);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1401_ = lean_apply_8(v_f_1313_, v_fvarId_1400_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1401_;
}
case 15:
{
lean_object* v_fvarId_1402_; lean_object* v___x_1403_; 
v_fvarId_1402_ = lean_ctor_get(v_e_1314_, 0);
lean_inc(v_fvarId_1402_);
lean_dec_ref_known(v_e_1314_, 1);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc(v___y_1315_);
v___x_1403_ = lean_apply_8(v_f_1313_, v_fvarId_1402_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1403_;
}
default: 
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_e_1314_);
lean_dec_ref(v_f_1313_);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v_args_1323_);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_nat_dec_lt(v___x_1324_, v___x_1325_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec_ref(v_args_1323_);
lean_dec_ref(v_f_1313_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
return v___x_1328_;
}
else
{
size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = lean_usize_of_nat(v___x_1325_);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1312_, v_f_1313_, v_args_1323_, v___x_1329_, v___x_1330_, v___x_1326_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v_args_1323_);
return v___x_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1406_, lean_object* v_f_1407_, lean_object* v_e_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v_pu_boxed_1416_; lean_object* v_res_1417_; 
v_pu_boxed_1416_ = lean_unbox(v_pu_1406_);
v_res_1417_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1416_, v_f_1407_, v_e_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec(v___y_1409_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1418_, lean_object* v_f_1419_, lean_object* v_decl_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_type_1428_; lean_object* v_value_1429_; lean_object* v___x_1430_; 
v_type_1428_ = lean_ctor_get(v_decl_1420_, 2);
lean_inc_ref(v_type_1428_);
v_value_1429_ = lean_ctor_get(v_decl_1420_, 3);
lean_inc(v_value_1429_);
lean_dec_ref(v_decl_1420_);
lean_inc_ref(v_f_1419_);
v___x_1430_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1419_, v_type_1428_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1430_, 1);
v___x_1431_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1418_, v_f_1419_, v_value_1429_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
return v___x_1431_;
}
else
{
lean_dec(v_value_1429_);
lean_dec_ref(v_f_1419_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1432_, lean_object* v_f_1433_, lean_object* v_decl_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v_pu_boxed_1442_; lean_object* v_res_1443_; 
v_pu_boxed_1442_ = lean_unbox(v_pu_1432_);
v_res_1443_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1442_, v_f_1433_, v_decl_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec(v___y_1435_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1444_, lean_object* v_f_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v_pu_boxed_1454_; lean_object* v_res_1455_; 
v_pu_boxed_1454_ = lean_unbox(v_pu_1444_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1454_, v_f_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1456_, lean_object* v_f_1457_, lean_object* v_as_1458_, size_t v_i_1459_, size_t v_stop_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_eq(v_i_1459_, v_stop_1460_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1470_ = lean_box(v_pu_1456_);
lean_inc_ref(v_f_1457_);
v___f_1471_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1471_, 0, v___x_1470_);
lean_closure_set(v___f_1471_, 1, v_f_1457_);
v___x_1472_ = lean_array_uget_borrowed(v_as_1458_, v_i_1459_);
lean_inc(v___x_1472_);
v___x_1473_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1472_, v___f_1471_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; size_t v___x_1475_; size_t v___x_1476_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1459_, v___x_1475_);
v_i_1459_ = v___x_1476_;
v_b_1461_ = v_a_1474_;
goto _start;
}
else
{
lean_dec_ref(v_f_1457_);
return v___x_1473_;
}
}
else
{
lean_object* v___x_1478_; 
lean_dec_ref(v_f_1457_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_b_1461_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1479_, lean_object* v_f_1480_, lean_object* v_c_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
switch(lean_obj_tag(v_c_1481_))
{
case 0:
{
lean_object* v_decl_1489_; lean_object* v_k_1490_; lean_object* v___x_1491_; 
v_decl_1489_ = lean_ctor_get(v_c_1481_, 0);
lean_inc_ref(v_decl_1489_);
v_k_1490_ = lean_ctor_get(v_c_1481_, 1);
lean_inc_ref(v_k_1490_);
lean_dec_ref_known(v_c_1481_, 2);
lean_inc_ref(v_f_1480_);
v___x_1491_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1479_, v_f_1480_, v_decl_1489_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
v_c_1481_ = v_k_1490_;
goto _start;
}
else
{
lean_dec_ref(v_k_1490_);
lean_dec_ref(v_f_1480_);
return v___x_1491_;
}
}
case 3:
{
lean_object* v_fvarId_1493_; lean_object* v_args_1494_; lean_object* v___x_1495_; 
v_fvarId_1493_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1493_);
v_args_1494_ = lean_ctor_get(v_c_1481_, 1);
lean_inc_ref(v_args_1494_);
lean_dec_ref_known(v_c_1481_, 2);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1495_ = lean_apply_8(v_f_1480_, v_fvarId_1493_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1510_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_array_get_size(v_args_1494_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_nat_dec_lt(v___x_1499_, v___x_1500_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref(v_args_1494_);
lean_dec_ref(v_f_1480_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1501_);
v___x_1504_ = v___x_1497_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
else
{
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1497_);
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = lean_usize_of_nat(v___x_1500_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1479_, v_f_1480_, v_args_1494_, v___x_1506_, v___x_1507_, v___x_1501_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_args_1494_);
return v___x_1508_;
}
}
}
else
{
lean_dec_ref(v_args_1494_);
lean_dec_ref(v_f_1480_);
return v___x_1495_;
}
}
case 4:
{
lean_object* v_cases_1511_; lean_object* v_resultType_1512_; lean_object* v_discr_1513_; lean_object* v_alts_1514_; lean_object* v___x_1515_; 
v_cases_1511_ = lean_ctor_get(v_c_1481_, 0);
lean_inc_ref(v_cases_1511_);
lean_dec_ref_known(v_c_1481_, 1);
v_resultType_1512_ = lean_ctor_get(v_cases_1511_, 1);
lean_inc_ref(v_resultType_1512_);
v_discr_1513_ = lean_ctor_get(v_cases_1511_, 2);
lean_inc(v_discr_1513_);
v_alts_1514_ = lean_ctor_get(v_cases_1511_, 3);
lean_inc_ref(v_alts_1514_);
lean_dec_ref(v_cases_1511_);
lean_inc_ref(v_f_1480_);
v___x_1515_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1480_, v_resultType_1512_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1515_, 1);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1516_ = lean_apply_8(v_f_1480_, v_discr_1513_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1516_, 0);
lean_dec(v_unused_1531_);
v___x_1518_ = v___x_1516_;
v_isShared_1519_ = v_isSharedCheck_1530_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v___x_1516_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1530_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_array_get_size(v_alts_1514_);
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_nat_dec_lt(v___x_1520_, v___x_1521_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1525_; 
lean_dec_ref(v_alts_1514_);
lean_dec_ref(v_f_1480_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1522_);
v___x_1525_ = v___x_1518_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1522_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
else
{
size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
lean_del_object(v___x_1518_);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = lean_usize_of_nat(v___x_1521_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1479_, v_f_1480_, v_alts_1514_, v___x_1527_, v___x_1528_, v___x_1522_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_alts_1514_);
return v___x_1529_;
}
}
}
else
{
lean_dec_ref(v_alts_1514_);
lean_dec_ref(v_f_1480_);
return v___x_1516_;
}
}
else
{
lean_dec_ref(v_alts_1514_);
lean_dec(v_discr_1513_);
lean_dec_ref(v_f_1480_);
return v___x_1515_;
}
}
case 5:
{
lean_object* v_fvarId_1532_; lean_object* v___x_1533_; 
v_fvarId_1532_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1532_);
lean_dec_ref_known(v_c_1481_, 1);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1533_ = lean_apply_8(v_f_1480_, v_fvarId_1532_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
return v___x_1533_;
}
case 6:
{
lean_object* v_type_1534_; lean_object* v___x_1535_; 
v_type_1534_ = lean_ctor_get(v_c_1481_, 0);
lean_inc_ref(v_type_1534_);
lean_dec_ref_known(v_c_1481_, 1);
v___x_1535_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1480_, v_type_1534_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1535_;
}
case 7:
{
lean_object* v_fvarId_1536_; lean_object* v_y_1537_; lean_object* v_k_1538_; lean_object* v___x_1539_; 
v_fvarId_1536_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1536_);
v_y_1537_ = lean_ctor_get(v_c_1481_, 2);
lean_inc(v_y_1537_);
v_k_1538_ = lean_ctor_get(v_c_1481_, 3);
lean_inc_ref(v_k_1538_);
lean_dec_ref_known(v_c_1481_, 4);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1539_ = lean_apply_8(v_f_1480_, v_fvarId_1536_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref_known(v___x_1539_, 1);
lean_inc_ref(v_f_1480_);
v___x_1540_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1480_, v_y_1537_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_dec_ref_known(v___x_1540_, 1);
v_c_1481_ = v_k_1538_;
goto _start;
}
else
{
lean_dec_ref(v_k_1538_);
lean_dec_ref(v_f_1480_);
return v___x_1540_;
}
}
else
{
lean_dec_ref(v_k_1538_);
lean_dec(v_y_1537_);
lean_dec_ref(v_f_1480_);
return v___x_1539_;
}
}
case 8:
{
lean_object* v_fvarId_1542_; lean_object* v_y_1543_; lean_object* v_k_1544_; lean_object* v___x_1545_; 
v_fvarId_1542_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1542_);
v_y_1543_ = lean_ctor_get(v_c_1481_, 2);
lean_inc(v_y_1543_);
v_k_1544_ = lean_ctor_get(v_c_1481_, 3);
lean_inc_ref(v_k_1544_);
lean_dec_ref_known(v_c_1481_, 4);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1545_ = lean_apply_8(v_f_1480_, v_fvarId_1542_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; 
lean_dec_ref_known(v___x_1545_, 1);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1546_ = lean_apply_8(v_f_1480_, v_y_1543_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
v_c_1481_ = v_k_1544_;
goto _start;
}
else
{
lean_dec_ref(v_k_1544_);
lean_dec_ref(v_f_1480_);
return v___x_1546_;
}
}
else
{
lean_dec_ref(v_k_1544_);
lean_dec(v_y_1543_);
lean_dec_ref(v_f_1480_);
return v___x_1545_;
}
}
case 9:
{
lean_object* v_fvarId_1548_; lean_object* v_y_1549_; lean_object* v_ty_1550_; lean_object* v_k_1551_; lean_object* v___x_1552_; 
v_fvarId_1548_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1548_);
v_y_1549_ = lean_ctor_get(v_c_1481_, 3);
lean_inc(v_y_1549_);
v_ty_1550_ = lean_ctor_get(v_c_1481_, 4);
lean_inc_ref(v_ty_1550_);
v_k_1551_ = lean_ctor_get(v_c_1481_, 5);
lean_inc_ref(v_k_1551_);
lean_dec_ref_known(v_c_1481_, 6);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1552_ = lean_apply_8(v_f_1480_, v_fvarId_1548_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref_known(v___x_1552_, 1);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1553_ = lean_apply_8(v_f_1480_, v_y_1549_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref_known(v___x_1553_, 1);
lean_inc_ref(v_f_1480_);
v___x_1554_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1480_, v_ty_1550_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref_known(v___x_1554_, 1);
v_c_1481_ = v_k_1551_;
goto _start;
}
else
{
lean_dec_ref(v_k_1551_);
lean_dec_ref(v_f_1480_);
return v___x_1554_;
}
}
else
{
lean_dec_ref(v_k_1551_);
lean_dec_ref(v_ty_1550_);
lean_dec_ref(v_f_1480_);
return v___x_1553_;
}
}
else
{
lean_dec_ref(v_k_1551_);
lean_dec_ref(v_ty_1550_);
lean_dec(v_y_1549_);
lean_dec_ref(v_f_1480_);
return v___x_1552_;
}
}
case 10:
{
lean_object* v_fvarId_1556_; lean_object* v_k_1557_; lean_object* v___x_1558_; 
v_fvarId_1556_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1556_);
v_k_1557_ = lean_ctor_get(v_c_1481_, 2);
lean_inc_ref(v_k_1557_);
lean_dec_ref_known(v_c_1481_, 3);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1558_ = lean_apply_8(v_f_1480_, v_fvarId_1556_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref_known(v___x_1558_, 1);
v_c_1481_ = v_k_1557_;
goto _start;
}
else
{
lean_dec_ref(v_k_1557_);
lean_dec_ref(v_f_1480_);
return v___x_1558_;
}
}
case 11:
{
lean_object* v_fvarId_1560_; lean_object* v_k_1561_; lean_object* v___x_1562_; 
v_fvarId_1560_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1560_);
v_k_1561_ = lean_ctor_get(v_c_1481_, 2);
lean_inc_ref(v_k_1561_);
lean_dec_ref_known(v_c_1481_, 3);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1562_ = lean_apply_8(v_f_1480_, v_fvarId_1560_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_dec_ref_known(v___x_1562_, 1);
v_c_1481_ = v_k_1561_;
goto _start;
}
else
{
lean_dec_ref(v_k_1561_);
lean_dec_ref(v_f_1480_);
return v___x_1562_;
}
}
case 12:
{
lean_object* v_fvarId_1564_; lean_object* v_k_1565_; lean_object* v___x_1566_; 
v_fvarId_1564_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1564_);
v_k_1565_ = lean_ctor_get(v_c_1481_, 3);
lean_inc_ref(v_k_1565_);
lean_dec_ref_known(v_c_1481_, 4);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1566_ = lean_apply_8(v_f_1480_, v_fvarId_1564_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_dec_ref_known(v___x_1566_, 1);
v_c_1481_ = v_k_1565_;
goto _start;
}
else
{
lean_dec_ref(v_k_1565_);
lean_dec_ref(v_f_1480_);
return v___x_1566_;
}
}
case 13:
{
lean_object* v_fvarId_1568_; lean_object* v_k_1569_; lean_object* v___x_1570_; 
v_fvarId_1568_ = lean_ctor_get(v_c_1481_, 0);
lean_inc(v_fvarId_1568_);
v_k_1569_ = lean_ctor_get(v_c_1481_, 1);
lean_inc_ref(v_k_1569_);
lean_dec_ref_known(v_c_1481_, 2);
lean_inc_ref(v_f_1480_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc(v___y_1482_);
v___x_1570_ = lean_apply_8(v_f_1480_, v_fvarId_1568_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_dec_ref_known(v___x_1570_, 1);
v_c_1481_ = v_k_1569_;
goto _start;
}
else
{
lean_dec_ref(v_k_1569_);
lean_dec_ref(v_f_1480_);
return v___x_1570_;
}
}
default: 
{
lean_object* v_decl_1572_; lean_object* v_k_1573_; lean_object* v_params_1574_; lean_object* v_type_1575_; lean_object* v_value_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v_decl_1572_ = lean_ctor_get(v_c_1481_, 0);
lean_inc_ref(v_decl_1572_);
v_k_1573_ = lean_ctor_get(v_c_1481_, 1);
lean_inc_ref(v_k_1573_);
lean_dec_ref(v_c_1481_);
v_params_1574_ = lean_ctor_get(v_decl_1572_, 2);
lean_inc_ref(v_params_1574_);
v_type_1575_ = lean_ctor_get(v_decl_1572_, 3);
lean_inc_ref(v_type_1575_);
v_value_1576_ = lean_ctor_get(v_decl_1572_, 4);
lean_inc_ref(v_value_1576_);
lean_dec_ref(v_decl_1572_);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_array_get_size(v_params_1574_);
v___x_1579_ = lean_nat_dec_lt(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v_params_1574_);
lean_inc_ref(v_f_1480_);
v___x_1580_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1480_, v_type_1575_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref_known(v___x_1580_, 1);
lean_inc_ref(v_f_1480_);
v___x_1581_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1479_, v_f_1480_, v_value_1576_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v_c_1481_ = v_k_1573_;
goto _start;
}
else
{
lean_dec_ref(v_k_1573_);
lean_dec_ref(v_f_1480_);
return v___x_1581_;
}
}
else
{
lean_dec_ref(v_value_1576_);
lean_dec_ref(v_k_1573_);
lean_dec_ref(v_f_1480_);
return v___x_1580_;
}
}
else
{
lean_object* v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = ((size_t)0ULL);
v___x_1585_ = lean_usize_of_nat(v___x_1578_);
lean_inc_ref(v_f_1480_);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1479_, v_f_1480_, v_params_1574_, v___x_1584_, v___x_1585_, v___x_1583_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_params_1574_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref_known(v___x_1586_, 1);
lean_inc_ref(v_f_1480_);
v___x_1587_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1480_, v_type_1575_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref_known(v___x_1587_, 1);
lean_inc_ref(v_f_1480_);
v___x_1588_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1479_, v_f_1480_, v_value_1576_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_dec_ref_known(v___x_1588_, 1);
v_c_1481_ = v_k_1573_;
goto _start;
}
else
{
lean_dec_ref(v_k_1573_);
lean_dec_ref(v_f_1480_);
return v___x_1588_;
}
}
else
{
lean_dec_ref(v_value_1576_);
lean_dec_ref(v_k_1573_);
lean_dec_ref(v_f_1480_);
return v___x_1587_;
}
}
else
{
lean_dec_ref(v_value_1576_);
lean_dec_ref(v_type_1575_);
lean_dec_ref(v_k_1573_);
lean_dec_ref(v_f_1480_);
return v___x_1586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1590_, lean_object* v_f_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1590_, v_f_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1601_, lean_object* v_f_1602_, lean_object* v_as_1603_, lean_object* v_i_1604_, lean_object* v_stop_1605_, lean_object* v_b_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
uint8_t v_pu_boxed_1614_; size_t v_i_boxed_1615_; size_t v_stop_boxed_1616_; lean_object* v_res_1617_; 
v_pu_boxed_1614_ = lean_unbox(v_pu_1601_);
v_i_boxed_1615_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_stop_boxed_1616_ = lean_unbox_usize(v_stop_1605_);
lean_dec(v_stop_1605_);
v_res_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1614_, v_f_1602_, v_as_1603_, v_i_boxed_1615_, v_stop_boxed_1616_, v_b_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v_as_1603_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1618_, lean_object* v_f_1619_, lean_object* v_c_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v_pu_boxed_1628_; lean_object* v_res_1629_; 
v_pu_boxed_1628_ = lean_unbox(v_pu_1618_);
v_res_1629_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1628_, v_f_1619_, v_c_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec(v___y_1621_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1630_, lean_object* v_as_1631_, size_t v_i_1632_, size_t v_stop_1633_, lean_object* v_b_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_usize_dec_eq(v_i_1632_, v_stop_1633_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_inc(v___x_1630_);
v___x_1643_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1643_, 0, v___x_1630_);
v___x_1644_ = lean_array_uget_borrowed(v_as_1631_, v_i_1632_);
lean_inc(v___x_1644_);
v___x_1645_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1643_, v___x_1644_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; size_t v___x_1647_; size_t v___x_1648_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1632_, v___x_1647_);
v_i_1632_ = v___x_1648_;
v_b_1634_ = v_a_1646_;
goto _start;
}
else
{
lean_dec(v___x_1630_);
return v___x_1645_;
}
}
else
{
lean_object* v___x_1650_; 
lean_dec(v___x_1630_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_b_1634_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1651_, lean_object* v_as_1652_, lean_object* v_i_1653_, lean_object* v_stop_1654_, lean_object* v_b_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
size_t v_i_boxed_1663_; size_t v_stop_boxed_1664_; lean_object* v_res_1665_; 
v_i_boxed_1663_ = lean_unbox_usize(v_i_1653_);
lean_dec(v_i_1653_);
v_stop_boxed_1664_ = lean_unbox_usize(v_stop_1654_);
lean_dec(v_stop_1654_);
v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1651_, v_as_1652_, v_i_boxed_1663_, v_stop_boxed_1664_, v_b_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v_as_1652_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = 0;
v___x_1675_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1666_);
lean_inc(v___x_1675_);
v___x_1676_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1676_, 0, v___x_1675_);
switch(lean_obj_tag(v_alt_1666_))
{
case 0:
{
lean_object* v_params_1677_; lean_object* v_code_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_params_1677_ = lean_ctor_get(v_alt_1666_, 1);
lean_inc_ref(v_params_1677_);
v_code_1678_ = lean_ctor_get(v_alt_1666_, 2);
lean_inc_ref(v_code_1678_);
lean_dec_ref_known(v_alt_1666_, 3);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_array_get_size(v_params_1677_);
v___x_1681_ = lean_nat_dec_lt(v___x_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v_params_1677_);
lean_dec(v___x_1675_);
v___x_1682_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1674_, v___x_1676_, v_code_1678_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = lean_box(0);
v___x_1684_ = ((size_t)0ULL);
v___x_1685_ = lean_usize_of_nat(v___x_1680_);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1675_, v_params_1677_, v___x_1684_, v___x_1685_, v___x_1683_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec_ref(v_params_1677_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1686_, 1);
v___x_1687_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1674_, v___x_1676_, v_code_1678_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1687_;
}
else
{
lean_dec_ref(v_code_1678_);
lean_dec_ref(v___x_1676_);
return v___x_1686_;
}
}
}
case 1:
{
lean_object* v_code_1688_; lean_object* v___x_1689_; 
lean_dec(v___x_1675_);
v_code_1688_ = lean_ctor_get(v_alt_1666_, 1);
lean_inc_ref(v_code_1688_);
lean_dec_ref_known(v_alt_1666_, 2);
v___x_1689_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1674_, v___x_1676_, v_code_1688_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1689_;
}
default: 
{
lean_object* v_code_1690_; lean_object* v___x_1691_; 
lean_dec(v___x_1675_);
v_code_1690_ = lean_ctor_get(v_alt_1666_, 0);
lean_inc_ref(v_code_1690_);
lean_dec_ref_known(v_alt_1666_, 1);
v___x_1691_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1674_, v___x_1676_, v_code_1690_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec(v_a_1693_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1701_, lean_object* v_f_1702_, lean_object* v_param_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1702_, v_param_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1712_, lean_object* v_f_1713_, lean_object* v_param_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_pu_boxed_1722_; lean_object* v_res_1723_; 
v_pu_boxed_1722_ = lean_unbox(v_pu_1712_);
v_res_1723_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1722_, v_f_1713_, v_param_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec(v___y_1715_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1724_, lean_object* v_alt_1725_, lean_object* v_f_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1725_, v_f_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1735_, lean_object* v_alt_1736_, lean_object* v_f_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_pu_boxed_1745_; lean_object* v_res_1746_; 
v_pu_boxed_1745_ = lean_unbox(v_pu_1735_);
v_res_1746_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1745_, v_alt_1736_, v_f_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec(v___y_1738_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1747_, lean_object* v_f_1748_, lean_object* v_arg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1748_, v_arg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1758_, lean_object* v_f_1759_, lean_object* v_arg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v_pu_boxed_1768_; lean_object* v_res_1769_; 
v_pu_boxed_1768_ = lean_unbox(v_pu_1758_);
v_res_1769_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1768_, v_f_1759_, v_arg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1770_, size_t v_i_1771_, size_t v_stop_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_usize_dec_eq(v_i_1771_, v_stop_1772_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_array_uget_borrowed(v_as_1770_, v_i_1771_);
lean_inc(v___x_1782_);
v___x_1783_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1782_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; size_t v___x_1785_; size_t v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_add(v_i_1771_, v___x_1785_);
v_i_1771_ = v___x_1786_;
v_b_1773_ = v_a_1784_;
goto _start;
}
else
{
return v___x_1783_;
}
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_b_1773_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1789_, lean_object* v_i_1790_, lean_object* v_stop_1791_, lean_object* v_b_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_i_boxed_1800_; size_t v_stop_boxed_1801_; lean_object* v_res_1802_; 
v_i_boxed_1800_ = lean_unbox_usize(v_i_1790_);
lean_dec(v_i_1790_);
v_stop_boxed_1801_ = lean_unbox_usize(v_stop_1791_);
lean_dec(v_stop_1791_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1789_, v_i_boxed_1800_, v_stop_boxed_1801_, v_b_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v_as_1789_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_alts_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v_alts_1811_ = lean_ctor_get(v_cs_1803_, 3);
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_array_get_size(v_alts_1811_);
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_nat_dec_lt(v___x_1812_, v___x_1813_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
return v___x_1816_;
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1813_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1811_, v___x_1817_, v___x_1818_, v___x_1814_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_cs_1820_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
if (lean_obj_tag(v_a_1829_) == 0)
{
lean_object* v___x_1831_; 
v___x_1831_ = l_List_reverse___redArg(v_a_1830_);
return v___x_1831_;
}
else
{
lean_object* v_head_1832_; lean_object* v_tail_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1844_; 
v_head_1832_ = lean_ctor_get(v_a_1829_, 0);
v_tail_1833_ = lean_ctor_get(v_a_1829_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1835_ = v_a_1829_;
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_tail_1833_);
lean_inc(v_head_1832_);
lean_dec(v_a_1829_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1837_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1832_);
lean_dec(v_head_1832_);
v___x_1838_ = lean_box(2);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v_a_1830_);
lean_ctor_set(v___x_1835_, 0, v___x_1839_);
v___x_1841_ = v___x_1835_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1830_);
v___x_1841_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
v_a_1829_ = v_tail_1833_;
v_a_1830_ = v___x_1841_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg(lean_object* v_as_x27_1845_, lean_object* v_b_1846_){
_start:
{
if (lean_obj_tag(v_as_x27_1845_) == 0)
{
return v_b_1846_;
}
else
{
lean_object* v_head_1847_; lean_object* v_tail_1848_; lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v_r_1851_; 
v_head_1847_ = lean_ctor_get(v_as_x27_1845_, 0);
v_tail_1848_ = lean_ctor_get(v_as_x27_1845_, 1);
v_fst_1849_ = lean_ctor_get(v_head_1847_, 0);
v_snd_1850_ = lean_ctor_get(v_head_1847_, 1);
lean_inc(v_snd_1850_);
lean_inc(v_fst_1849_);
v_r_1851_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_b_1846_, v_fst_1849_, v_snd_1850_);
v_as_x27_1845_ = v_tail_1848_;
v_b_1846_ = v_r_1851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg___boxed(lean_object* v_as_x27_1853_, lean_object* v_b_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg(v_as_x27_1853_, v_b_1854_);
lean_dec(v_as_x27_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(lean_object* v_m_1856_, lean_object* v_l_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg(v_l_1857_, v_m_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1___boxed(lean_object* v_m_1859_, lean_object* v_l_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(v_m_1859_, v_l_1860_);
lean_dec(v_l_1860_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg(lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_x_1862_);
return v___x_1869_;
}
else
{
lean_object* v_head_1870_; lean_object* v_tail_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1933_; 
v_head_1870_ = lean_ctor_get(v_x_1863_, 0);
v_tail_1871_ = lean_ctor_get(v_x_1863_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1863_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1873_ = v_x_1863_;
v_isShared_1874_ = v_isSharedCheck_1933_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_tail_1871_);
lean_inc(v_head_1870_);
lean_dec(v_x_1863_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1933_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1932_; 
v_fst_1875_ = lean_ctor_get(v_x_1862_, 0);
v_snd_1876_ = lean_ctor_get(v_x_1862_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x_1862_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1878_ = v_x_1862_;
v_isShared_1879_ = v_isSharedCheck_1932_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_snd_1876_);
lean_inc(v_fst_1875_);
lean_dec(v_x_1862_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1932_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; 
if (lean_obj_tag(v_head_1870_) == 0)
{
lean_object* v_decl_1913_; lean_object* v___x_1914_; 
v_decl_1913_ = lean_ctor_get(v_head_1870_, 0);
lean_inc_ref(v_decl_1913_);
v___x_1914_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_1913_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; uint8_t v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1916_ = lean_unbox(v_a_1915_);
lean_dec(v_a_1915_);
if (v___x_1916_ == 0)
{
lean_del_object(v___x_1873_);
v___y_1881_ = v___y_1864_;
v___y_1882_ = v___y_1865_;
v___y_1883_ = v___y_1866_;
v___y_1884_ = v___y_1867_;
goto v___jp_1880_;
}
else
{
lean_object* v_fvarId_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_inc_ref(v_decl_1913_);
lean_dec_ref_known(v_head_1870_, 1);
lean_del_object(v___x_1878_);
v_fvarId_1917_ = lean_ctor_get(v_decl_1913_, 0);
lean_inc(v_fvarId_1917_);
lean_dec_ref(v_decl_1913_);
v___x_1918_ = lean_box(2);
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1875_, v_fvarId_1917_, v___x_1918_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 0);
lean_ctor_set(v___x_1873_, 1, v_snd_1876_);
lean_ctor_set(v___x_1873_, 0, v___x_1919_);
v___x_1921_ = v___x_1873_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_snd_1876_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
v_x_1862_ = v___x_1921_;
v_x_1863_ = v_tail_1871_;
goto _start;
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref_known(v_head_1870_, 1);
lean_del_object(v___x_1878_);
lean_dec(v_snd_1876_);
lean_dec(v_fst_1875_);
lean_del_object(v___x_1873_);
lean_dec(v_tail_1871_);
v_a_1924_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1914_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1914_);
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
else
{
lean_del_object(v___x_1873_);
v___y_1881_ = v___y_1864_;
v___y_1882_ = v___y_1865_;
v___y_1883_ = v___y_1866_;
v___y_1884_ = v___y_1867_;
goto v___jp_1880_;
}
v___jp_1880_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_st_ref_get(v___y_1884_);
lean_dec(v___x_1885_);
v___x_1886_ = lean_st_mk_ref(v_snd_1876_);
lean_inc(v_head_1870_);
v___x_1887_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1870_, v___x_1886_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = lean_st_ref_get(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_unbox(v_a_1888_);
lean_dec(v_a_1888_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1891_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1870_);
lean_dec(v_head_1870_);
v___x_1892_ = lean_box(3);
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1875_, v___x_1891_, v___x_1892_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1889_);
lean_ctor_set(v___x_1878_, 0, v___x_1893_);
v___x_1895_ = v___x_1878_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1889_);
v___x_1895_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
v_x_1862_ = v___x_1895_;
v_x_1863_ = v_tail_1871_;
goto _start;
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1898_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1870_);
lean_dec(v_head_1870_);
v___x_1899_ = lean_box(2);
v___x_1900_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1875_, v___x_1898_, v___x_1899_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1889_);
lean_ctor_set(v___x_1878_, 0, v___x_1900_);
v___x_1902_ = v___x_1878_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1889_);
v___x_1902_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v_x_1862_ = v___x_1902_;
v_x_1863_ = v_tail_1871_;
goto _start;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v___x_1886_);
lean_del_object(v___x_1878_);
lean_dec(v_fst_1875_);
lean_dec(v_tail_1871_);
lean_dec(v_head_1870_);
v_a_1905_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1887_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1887_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg___boxed(lean_object* v_x_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg(v_x_1934_, v_x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1941_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_unsigned_to_nat(16u);
v___x_1944_ = lean_mk_array(v___x_1943_, v___x_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0);
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_map_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v_typeName_1990_; lean_object* v_discr_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_typeName_1990_ = lean_ctor_get(v_cs_1957_, 0);
v_discr_1991_ = lean_ctor_get(v_cs_1957_, 2);
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_box(0);
v___x_2000_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4));
v___x_2001_ = lean_name_eq(v_typeName_1990_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6));
v___x_2003_ = lean_name_eq(v_typeName_1990_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2004_ = l_List_lengthTR___redArg(v_a_1958_);
v___x_2005_ = lean_unsigned_to_nat(4u);
v___x_2006_ = lean_nat_mul(v___x_2004_, v___x_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_unsigned_to_nat(3u);
v___x_2008_ = lean_nat_div(v___x_2006_, v___x_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = l_Nat_nextPowerOfTwo(v___x_2008_);
lean_dec(v___x_2008_);
v___x_2010_ = lean_mk_array(v___x_2009_, v___x_1993_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_1992_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
lean_inc(v_a_1958_);
v___x_2014_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg(v___x_2013_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v_fst_2016_; uint8_t v___x_2017_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v_fst_2016_ = lean_ctor_get(v_a_2015_, 0);
lean_inc(v_fst_2016_);
lean_dec(v_a_2015_);
v___x_2017_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2016_, v_discr_1991_);
if (v___x_2017_ == 0)
{
v_map_1965_ = v_fst_2016_;
v___y_1966_ = v_a_1958_;
v___y_1967_ = v_a_1959_;
v___y_1968_ = v_a_1960_;
v___y_1969_ = v_a_1961_;
v___y_1970_ = v_a_1962_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_box(2);
lean_inc(v_discr_1991_);
v___x_2019_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2016_, v_discr_1991_, v___x_2018_);
v_map_1965_ = v___x_2019_;
v___y_1966_ = v_a_1958_;
v___y_1967_ = v_a_1959_;
v___y_1968_ = v_a_1960_;
v___y_1969_ = v_a_1961_;
v___y_1970_ = v_a_1962_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v_cs_1957_);
v_a_2020_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2014_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2014_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
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
lean_dec_ref(v_cs_1957_);
goto v___jp_1994_;
}
}
else
{
lean_dec_ref(v_cs_1957_);
goto v___jp_1994_;
}
v___jp_1964_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_st_mk_ref(v_map_1965_);
v___x_1972_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1957_, v___x_1971_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec_ref(v_cs_1957_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v___x_1972_, 0);
lean_dec(v_unused_1981_);
v___x_1974_ = v___x_1972_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v___x_1972_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_st_ref_get(v___x_1971_);
lean_dec(v___x_1971_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v___x_1971_);
v_a_1982_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1972_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1972_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
v___jp_1994_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1995_ = lean_box(0);
lean_inc(v_a_1958_);
v___x_1996_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_a_1958_, v___x_1995_);
v___x_1997_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_1998_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg(v___x_1996_, v___x_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___redArg(v_x_2036_, v_x_2037_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___boxed(lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(v_x_2045_, v_x_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1(lean_object* v_as_2054_, lean_object* v_as_x27_2055_, lean_object* v_b_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___redArg(v_as_x27_2055_, v_b_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1___boxed(lean_object* v_as_2059_, lean_object* v_as_x27_2060_, lean_object* v_b_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1_spec__1(v_as_2059_, v_as_x27_2060_, v_b_2061_, v_a_2062_);
lean_dec(v_as_x27_2060_);
lean_dec(v_as_2059_);
return v_res_2063_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_a_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2065_) == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = 0;
return v___x_2066_;
}
else
{
lean_object* v_key_2067_; lean_object* v_tail_2068_; uint8_t v___x_2069_; 
v_key_2067_ = lean_ctor_get(v_x_2065_, 0);
v_tail_2068_ = lean_ctor_get(v_x_2065_, 2);
v___x_2069_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2067_, v_a_2064_);
if (v___x_2069_ == 0)
{
v_x_2065_ = v_tail_2068_;
goto _start;
}
else
{
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_a_2071_, lean_object* v_x_2072_){
_start:
{
uint8_t v_res_2073_; lean_object* v_r_2074_; 
v_res_2073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2071_, v_x_2072_);
lean_dec(v_x_2072_);
lean_dec(v_a_2071_);
v_r_2074_ = lean_box(v_res_2073_);
return v_r_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object* v_a_2075_, lean_object* v_b_2076_, lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_dec(v_b_2076_);
lean_dec(v_a_2075_);
return v_x_2077_;
}
else
{
lean_object* v_key_2078_; lean_object* v_value_2079_; lean_object* v_tail_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2092_; 
v_key_2078_ = lean_ctor_get(v_x_2077_, 0);
v_value_2079_ = lean_ctor_get(v_x_2077_, 1);
v_tail_2080_ = lean_ctor_get(v_x_2077_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2082_ = v_x_2077_;
v_isShared_2083_ = v_isSharedCheck_2092_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_tail_2080_);
lean_inc(v_value_2079_);
lean_inc(v_key_2078_);
lean_dec(v_x_2077_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2092_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2078_, v_a_2075_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2075_, v_b_2076_, v_tail_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 2, v___x_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_key_2078_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_value_2079_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
else
{
lean_object* v___x_2090_; 
lean_dec(v_value_2079_);
lean_dec(v_key_2078_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_b_2076_);
lean_ctor_set(v___x_2082_, 0, v_a_2075_);
v___x_2090_ = v___x_2082_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2075_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_b_2076_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_tail_2080_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2094_) == 0)
{
return v_x_2093_;
}
else
{
lean_object* v_key_2095_; lean_object* v_value_2096_; lean_object* v_tail_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2120_; 
v_key_2095_ = lean_ctor_get(v_x_2094_, 0);
v_value_2096_ = lean_ctor_get(v_x_2094_, 1);
v_tail_2097_ = lean_ctor_get(v_x_2094_, 2);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_x_2094_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2099_ = v_x_2094_;
v_isShared_2100_ = v_isSharedCheck_2120_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_tail_2097_);
lean_inc(v_value_2096_);
lean_inc(v_key_2095_);
lean_dec(v_x_2094_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2120_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; uint64_t v___x_2104_; uint64_t v_fold_2105_; uint64_t v___x_2106_; uint64_t v___x_2107_; uint64_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2101_ = lean_array_get_size(v_x_2093_);
v___x_2102_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_2095_);
v___x_2103_ = 32ULL;
v___x_2104_ = lean_uint64_shift_right(v___x_2102_, v___x_2103_);
v_fold_2105_ = lean_uint64_xor(v___x_2102_, v___x_2104_);
v___x_2106_ = 16ULL;
v___x_2107_ = lean_uint64_shift_right(v_fold_2105_, v___x_2106_);
v___x_2108_ = lean_uint64_xor(v_fold_2105_, v___x_2107_);
v___x_2109_ = lean_uint64_to_usize(v___x_2108_);
v___x_2110_ = lean_usize_of_nat(v___x_2101_);
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_sub(v___x_2110_, v___x_2111_);
v___x_2113_ = lean_usize_land(v___x_2109_, v___x_2112_);
v___x_2114_ = lean_array_uget_borrowed(v_x_2093_, v___x_2113_);
lean_inc(v___x_2114_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 2, v___x_2114_);
v___x_2116_ = v___x_2099_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_key_2095_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_value_2096_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_array_uset(v_x_2093_, v___x_2113_, v___x_2116_);
v_x_2093_ = v___x_2117_;
v_x_2094_ = v_tail_2097_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2121_, lean_object* v_source_2122_, lean_object* v_target_2123_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_array_get_size(v_source_2122_);
v___x_2125_ = lean_nat_dec_lt(v_i_2121_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v_source_2122_);
lean_dec(v_i_2121_);
return v_target_2123_;
}
else
{
lean_object* v_es_2126_; lean_object* v___x_2127_; lean_object* v_source_2128_; lean_object* v_target_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_es_2126_ = lean_array_fget(v_source_2122_, v_i_2121_);
v___x_2127_ = lean_box(0);
v_source_2128_ = lean_array_fset(v_source_2122_, v_i_2121_, v___x_2127_);
v_target_2129_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2123_, v_es_2126_);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_add(v_i_2121_, v___x_2130_);
lean_dec(v_i_2121_);
v_i_2121_ = v___x_2131_;
v_source_2122_ = v_source_2128_;
v_target_2123_ = v_target_2129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object* v_data_2133_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_nbuckets_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2134_ = lean_array_get_size(v_data_2133_);
v___x_2135_ = lean_unsigned_to_nat(2u);
v_nbuckets_2136_ = lean_nat_mul(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_mk_array(v_nbuckets_2136_, v___x_2138_);
v___x_2140_ = lean_array_propagate_mark(v_data_2133_, v___x_2139_);
v___x_2141_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2137_, v_data_2133_, v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_){
_start:
{
lean_object* v_size_2145_; lean_object* v_buckets_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2189_; 
v_size_2145_ = lean_ctor_get(v_m_2142_, 0);
v_buckets_2146_ = lean_ctor_get(v_m_2142_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_m_2142_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2148_ = v_m_2142_;
v_isShared_2149_ = v_isSharedCheck_2189_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_buckets_2146_);
lean_inc(v_size_2145_);
lean_dec(v_m_2142_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2189_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; uint64_t v___x_2151_; uint64_t v___x_2152_; uint64_t v___x_2153_; uint64_t v_fold_2154_; uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; lean_object* v_bkt_2163_; uint8_t v___x_2164_; 
v___x_2150_ = lean_array_get_size(v_buckets_2146_);
v___x_2151_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2143_);
v___x_2152_ = 32ULL;
v___x_2153_ = lean_uint64_shift_right(v___x_2151_, v___x_2152_);
v_fold_2154_ = lean_uint64_xor(v___x_2151_, v___x_2153_);
v___x_2155_ = 16ULL;
v___x_2156_ = lean_uint64_shift_right(v_fold_2154_, v___x_2155_);
v___x_2157_ = lean_uint64_xor(v_fold_2154_, v___x_2156_);
v___x_2158_ = lean_uint64_to_usize(v___x_2157_);
v___x_2159_ = lean_usize_of_nat(v___x_2150_);
v___x_2160_ = ((size_t)1ULL);
v___x_2161_ = lean_usize_sub(v___x_2159_, v___x_2160_);
v___x_2162_ = lean_usize_land(v___x_2158_, v___x_2161_);
v_bkt_2163_ = lean_array_uget_borrowed(v_buckets_2146_, v___x_2162_);
v___x_2164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2143_, v_bkt_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v_size_x27_2166_; lean_object* v___x_2167_; lean_object* v_buckets_x27_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v_size_x27_2166_ = lean_nat_add(v_size_2145_, v___x_2165_);
lean_dec(v_size_2145_);
lean_inc(v_bkt_2163_);
v___x_2167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2167_, 0, v_a_2143_);
lean_ctor_set(v___x_2167_, 1, v_b_2144_);
lean_ctor_set(v___x_2167_, 2, v_bkt_2163_);
v_buckets_x27_2168_ = lean_array_uset(v_buckets_2146_, v___x_2162_, v___x_2167_);
v___x_2169_ = lean_unsigned_to_nat(4u);
v___x_2170_ = lean_nat_mul(v_size_x27_2166_, v___x_2169_);
v___x_2171_ = lean_unsigned_to_nat(3u);
v___x_2172_ = lean_nat_div(v___x_2170_, v___x_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_array_get_size(v_buckets_x27_2168_);
v___x_2174_ = lean_nat_dec_le(v___x_2172_, v___x_2173_);
lean_dec(v___x_2172_);
if (v___x_2174_ == 0)
{
lean_object* v_val_2175_; lean_object* v___x_2177_; 
v_val_2175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2168_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_val_2175_);
lean_ctor_set(v___x_2148_, 0, v_size_x27_2166_);
v___x_2177_ = v___x_2148_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_size_x27_2166_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_val_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
else
{
lean_object* v___x_2180_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_buckets_x27_2168_);
lean_ctor_set(v___x_2148_, 0, v_size_x27_2166_);
v___x_2180_ = v___x_2148_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_size_x27_2166_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_buckets_x27_2168_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v___x_2182_; lean_object* v_buckets_x27_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_inc(v_bkt_2163_);
v___x_2182_ = lean_box(0);
v_buckets_x27_2183_ = lean_array_uset(v_buckets_2146_, v___x_2162_, v___x_2182_);
v___x_2184_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2143_, v_b_2144_, v_bkt_2163_);
v___x_2185_ = lean_array_uset(v_buckets_x27_2183_, v___x_2162_, v___x_2184_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2185_);
v___x_2187_ = v___x_2148_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_size_2145_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2190_, size_t v_i_2191_, size_t v_stop_2192_, lean_object* v_b_2193_){
_start:
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_usize_dec_eq(v_i_2191_, v_stop_2192_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2195_ = lean_box(0);
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_sub(v_i_2191_, v___x_2196_);
v___x_2198_ = lean_array_uget_borrowed(v_as_2190_, v___x_2197_);
v___x_2199_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2198_);
v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2193_, v___x_2199_, v___x_2195_);
v_i_2191_ = v___x_2197_;
v_b_2193_ = v___x_2200_;
goto _start;
}
else
{
return v_b_2193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2202_, lean_object* v_i_2203_, lean_object* v_stop_2204_, lean_object* v_b_2205_){
_start:
{
size_t v_i_boxed_2206_; size_t v_stop_boxed_2207_; lean_object* v_res_2208_; 
v_i_boxed_2206_ = lean_unbox_usize(v_i_2203_);
lean_dec(v_i_2203_);
v_stop_boxed_2207_ = lean_unbox_usize(v_stop_2204_);
lean_dec(v_stop_2204_);
v_res_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2202_, v_i_boxed_2206_, v_stop_boxed_2207_, v_b_2205_);
lean_dec_ref(v_as_2202_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2209_){
_start:
{
lean_object* v_alts_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_map_2225_; uint8_t v___x_2226_; 
v_alts_2210_ = lean_ctor_get(v_cs_2209_, 3);
v___x_2211_ = lean_array_get_size(v_alts_2210_);
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_add(v___x_2211_, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_unsigned_to_nat(4u);
v___x_2216_ = lean_nat_mul(v___x_2213_, v___x_2215_);
lean_dec(v___x_2213_);
v___x_2217_ = lean_unsigned_to_nat(3u);
v___x_2218_ = lean_nat_div(v___x_2216_, v___x_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = l_Nat_nextPowerOfTwo(v___x_2218_);
lean_dec(v___x_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_mk_array(v___x_2219_, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2214_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_box(2);
v___x_2224_ = lean_box(0);
v_map_2225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2222_, v___x_2223_, v___x_2224_);
v___x_2226_ = lean_nat_dec_lt(v___x_2214_, v___x_2211_);
if (v___x_2226_ == 0)
{
return v_map_2225_;
}
else
{
size_t v___x_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_usize_of_nat(v___x_2211_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2210_, v___x_2227_, v___x_2228_, v_map_2225_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2230_);
lean_dec_ref(v_cs_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2232_, lean_object* v_m_2233_, lean_object* v_a_2234_, lean_object* v_b_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2233_, v_a_2234_, v_b_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2237_, lean_object* v_a_2238_, lean_object* v_x_2239_){
_start:
{
uint8_t v___x_2240_; 
v___x_2240_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2238_, v_x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_a_2242_, lean_object* v_x_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2241_, v_a_2242_, v_x_2243_);
lean_dec(v_x_2243_);
lean_dec(v_a_2242_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2246_, lean_object* v_data_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2249_, lean_object* v_a_2250_, lean_object* v_b_2251_, lean_object* v_x_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2250_, v_b_2251_, v_x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2254_, lean_object* v_i_2255_, lean_object* v_source_2256_, lean_object* v_target_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2255_, v_source_2256_, v_target_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2260_, v_x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___x_2266_; lean_object* v_decision_2267_; uint8_t v___x_2268_; 
v___x_2266_ = lean_st_ref_get(v_a_2264_);
v_decision_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc_ref(v_decision_2267_);
lean_dec(v___x_2266_);
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2267_, v_fvar_2263_);
lean_dec_ref(v_decision_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_fvar_2263_);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v_decision_2272_; lean_object* v_newArms_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2285_; 
v___x_2271_ = lean_st_ref_take(v_a_2264_);
v_decision_2272_ = lean_ctor_get(v___x_2271_, 0);
v_newArms_2273_ = lean_ctor_get(v___x_2271_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2275_ = v___x_2271_;
v_isShared_2276_ = v_isSharedCheck_2285_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_newArms_2273_);
lean_inc(v_decision_2272_);
lean_dec(v___x_2271_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2285_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = lean_box(2);
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2272_, v_fvar_2263_, v___x_2278_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2279_);
v___x_2281_ = v___x_2275_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_newArms_2273_);
v___x_2281_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_st_ref_put(v_a_2264_, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2277_);
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2286_, v_a_2287_);
lean_dec(v_a_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2290_, v_a_2291_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec(v_a_2300_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_toApplicative_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2381_; 
v___x_2316_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2317_ = l_StateRefT_x27_instMonad___redArg(v___x_2316_);
v_toApplicative_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v___x_2317_, 1);
lean_dec(v_unused_2382_);
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2381_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_toApplicative_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2381_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_toFunctor_2322_; lean_object* v_toSeq_2323_; lean_object* v_toSeqLeft_2324_; lean_object* v_toSeqRight_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2379_; 
v_toFunctor_2322_ = lean_ctor_get(v_toApplicative_2318_, 0);
v_toSeq_2323_ = lean_ctor_get(v_toApplicative_2318_, 2);
v_toSeqLeft_2324_ = lean_ctor_get(v_toApplicative_2318_, 3);
v_toSeqRight_2325_ = lean_ctor_get(v_toApplicative_2318_, 4);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_toApplicative_2318_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; 
v_unused_2380_ = lean_ctor_get(v_toApplicative_2318_, 1);
lean_dec(v_unused_2380_);
v___x_2327_ = v_toApplicative_2318_;
v_isShared_2328_ = v_isSharedCheck_2379_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_toSeqRight_2325_);
lean_inc(v_toSeqLeft_2324_);
lean_inc(v_toSeq_2323_);
lean_inc(v_toFunctor_2322_);
lean_dec(v_toApplicative_2318_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2379_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___f_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___f_2336_; lean_object* v___x_2338_; 
v___f_2329_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2330_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2322_);
v___f_2331_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2331_, 0, v_toFunctor_2322_);
v___f_2332_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2332_, 0, v_toFunctor_2322_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___f_2331_);
lean_ctor_set(v___x_2333_, 1, v___f_2332_);
v___f_2334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2334_, 0, v_toSeqRight_2325_);
v___f_2335_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2335_, 0, v_toSeqLeft_2324_);
v___f_2336_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2336_, 0, v_toSeq_2323_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 4, v___f_2334_);
lean_ctor_set(v___x_2327_, 3, v___f_2335_);
lean_ctor_set(v___x_2327_, 2, v___f_2336_);
lean_ctor_set(v___x_2327_, 1, v___f_2329_);
lean_ctor_set(v___x_2327_, 0, v___x_2333_);
v___x_2338_ = v___x_2327_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___f_2329_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v___f_2336_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v___f_2335_);
lean_ctor_set(v_reuseFailAlloc_2378_, 4, v___f_2334_);
v___x_2338_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2340_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___f_2330_);
lean_ctor_set(v___x_2320_, 0, v___x_2338_);
v___x_2340_ = v___x_2320_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___f_2330_);
v___x_2340_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; lean_object* v_toApplicative_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2375_; 
v___x_2341_ = l_StateRefT_x27_instMonad___redArg(v___x_2340_);
v_toApplicative_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2341_, 1);
lean_dec(v_unused_2376_);
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2375_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_toApplicative_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2375_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_toFunctor_2346_; lean_object* v_toSeq_2347_; lean_object* v_toSeqLeft_2348_; lean_object* v_toSeqRight_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2373_; 
v_toFunctor_2346_ = lean_ctor_get(v_toApplicative_2342_, 0);
v_toSeq_2347_ = lean_ctor_get(v_toApplicative_2342_, 2);
v_toSeqLeft_2348_ = lean_ctor_get(v_toApplicative_2342_, 3);
v_toSeqRight_2349_ = lean_ctor_get(v_toApplicative_2342_, 4);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_toApplicative_2342_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v_toApplicative_2342_, 1);
lean_dec(v_unused_2374_);
v___x_2351_ = v_toApplicative_2342_;
v_isShared_2352_ = v_isSharedCheck_2373_;
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
v_isShared_2352_ = v_isSharedCheck_2373_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___f_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___f_2360_; lean_object* v___x_2362_; 
v___f_2353_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2354_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
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
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v___f_2353_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v___f_2360_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v___f_2359_);
lean_ctor_set(v_reuseFailAlloc_2372_, 4, v___f_2358_);
v___x_2362_ = v_reuseFailAlloc_2372_;
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
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___f_2354_);
v___x_2364_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_10726__overap_2369_; lean_object* v___x_2370_; 
v___x_2365_ = l_ReaderT_instMonad___redArg(v___x_2364_);
v___x_2366_ = l_StateRefT_x27_instMonad___redArg(v___x_2365_);
v___x_2367_ = lean_box(0);
v___x_2368_ = l_instInhabitedOfMonad___redArg(v___x_2366_, v___x_2367_);
v___x_10726__overap_2369_ = lean_panic_fn_borrowed(v___x_2368_, v_msg_2308_);
lean_dec(v___x_2368_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v___y_2312_);
lean_inc_ref(v___y_2311_);
lean_inc(v___y_2310_);
lean_inc(v___y_2309_);
v___x_2370_ = lean_apply_7(v___x_10726__overap_2369_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, lean_box(0));
return v___x_2370_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec(v___y_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2392_, lean_object* v_e_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_ty_2402_; lean_object* v_body_2403_; uint8_t v___x_2406_; 
v___x_2406_ = l_Lean_Expr_hasFVar(v_e_2393_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_e_2393_);
lean_dec_ref(v_f_2392_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
else
{
switch(lean_obj_tag(v_e_2393_))
{
case 1:
{
lean_object* v_fvarId_2409_; lean_object* v___x_2410_; 
v_fvarId_2409_ = lean_ctor_get(v_e_2393_, 0);
lean_inc(v_fvarId_2409_);
lean_dec_ref_known(v_e_2393_, 1);
lean_inc(v___y_2399_);
lean_inc_ref(v___y_2398_);
lean_inc(v___y_2397_);
lean_inc_ref(v___y_2396_);
lean_inc(v___y_2395_);
lean_inc(v___y_2394_);
v___x_2410_ = lean_apply_8(v_f_2392_, v_fvarId_2409_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, lean_box(0));
return v___x_2410_;
}
case 2:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref_known(v_e_2393_, 1);
lean_dec_ref(v_f_2392_);
v___x_2411_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2412_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2411_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2412_;
}
case 5:
{
lean_object* v_fn_2413_; lean_object* v_arg_2414_; lean_object* v___x_2415_; 
v_fn_2413_ = lean_ctor_get(v_e_2393_, 0);
lean_inc_ref(v_fn_2413_);
v_arg_2414_ = lean_ctor_get(v_e_2393_, 1);
lean_inc_ref(v_arg_2414_);
lean_dec_ref_known(v_e_2393_, 2);
lean_inc_ref(v_f_2392_);
v___x_2415_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2392_, v_fn_2413_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_dec_ref_known(v___x_2415_, 1);
v_e_2393_ = v_arg_2414_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2414_);
lean_dec_ref(v_f_2392_);
return v___x_2415_;
}
}
case 6:
{
lean_object* v_binderType_2417_; lean_object* v_body_2418_; 
v_binderType_2417_ = lean_ctor_get(v_e_2393_, 1);
lean_inc_ref(v_binderType_2417_);
v_body_2418_ = lean_ctor_get(v_e_2393_, 2);
lean_inc_ref(v_body_2418_);
lean_dec_ref_known(v_e_2393_, 3);
v_ty_2402_ = v_binderType_2417_;
v_body_2403_ = v_body_2418_;
goto v___jp_2401_;
}
case 7:
{
lean_object* v_binderType_2419_; lean_object* v_body_2420_; 
v_binderType_2419_ = lean_ctor_get(v_e_2393_, 1);
lean_inc_ref(v_binderType_2419_);
v_body_2420_ = lean_ctor_get(v_e_2393_, 2);
lean_inc_ref(v_body_2420_);
lean_dec_ref_known(v_e_2393_, 3);
v_ty_2402_ = v_binderType_2419_;
v_body_2403_ = v_body_2420_;
goto v___jp_2401_;
}
case 8:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref_known(v_e_2393_, 4);
lean_dec_ref(v_f_2392_);
v___x_2421_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2422_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2421_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2422_;
}
case 11:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec_ref_known(v_e_2393_, 3);
lean_dec_ref(v_f_2392_);
v___x_2423_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2424_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2423_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2424_;
}
default: 
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec_ref(v_e_2393_);
lean_dec_ref(v_f_2392_);
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
}
v___jp_2401_:
{
lean_object* v___x_2404_; 
lean_inc_ref(v_f_2392_);
v___x_2404_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2392_, v_ty_2402_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_dec_ref_known(v___x_2404_, 1);
v_e_2393_ = v_body_2403_;
goto _start;
}
else
{
lean_dec_ref(v_body_2403_);
lean_dec_ref(v_f_2392_);
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2427_, lean_object* v_e_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2427_, v_e_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec(v___y_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2437_, lean_object* v_arg_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
switch(lean_obj_tag(v_arg_2438_))
{
case 0:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec_ref(v_f_2437_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
case 1:
{
lean_object* v_fvarId_2448_; lean_object* v___x_2449_; 
v_fvarId_2448_ = lean_ctor_get(v_arg_2438_, 0);
lean_inc(v_fvarId_2448_);
lean_dec_ref_known(v_arg_2438_, 1);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc(v___y_2440_);
lean_inc(v___y_2439_);
v___x_2449_ = lean_apply_8(v_f_2437_, v_fvarId_2448_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, lean_box(0));
return v___x_2449_;
}
default: 
{
lean_object* v_expr_2450_; lean_object* v___x_2451_; 
v_expr_2450_ = lean_ctor_get(v_arg_2438_, 0);
lean_inc_ref(v_expr_2450_);
lean_dec_ref_known(v_arg_2438_, 1);
v___x_2451_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2437_, v_expr_2450_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2452_, lean_object* v_arg_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2452_, v_arg_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec(v___y_2454_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2462_, lean_object* v_param_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_type_2471_; lean_object* v___x_2472_; 
v_type_2471_ = lean_ctor_get(v_param_2463_, 2);
lean_inc_ref(v_type_2471_);
lean_dec_ref(v_param_2463_);
v___x_2472_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2462_, v_type_2471_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2473_, lean_object* v_param_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2473_, v_param_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec(v___y_2475_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2483_, lean_object* v_f_2484_, lean_object* v_as_2485_, size_t v_i_2486_, size_t v_stop_2487_, lean_object* v_b_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_eq(v_i_2486_, v_stop_2487_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_array_uget_borrowed(v_as_2485_, v_i_2486_);
lean_inc(v___x_2497_);
lean_inc_ref(v_f_2484_);
v___x_2498_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2484_, v___x_2497_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; size_t v___x_2500_; size_t v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2486_, v___x_2500_);
v_i_2486_ = v___x_2501_;
v_b_2488_ = v_a_2499_;
goto _start;
}
else
{
lean_dec_ref(v_f_2484_);
return v___x_2498_;
}
}
else
{
lean_object* v___x_2503_; 
lean_dec_ref(v_f_2484_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_b_2488_);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2504_, lean_object* v_f_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_stop_2508_, lean_object* v_b_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
uint8_t v_pu_boxed_2517_; size_t v_i_boxed_2518_; size_t v_stop_boxed_2519_; lean_object* v_res_2520_; 
v_pu_boxed_2517_ = lean_unbox(v_pu_2504_);
v_i_boxed_2518_ = lean_unbox_usize(v_i_2507_);
lean_dec(v_i_2507_);
v_stop_boxed_2519_ = lean_unbox_usize(v_stop_2508_);
lean_dec(v_stop_2508_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2517_, v_f_2505_, v_as_2506_, v_i_boxed_2518_, v_stop_boxed_2519_, v_b_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v_as_2506_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2521_, lean_object* v_f_2522_, lean_object* v_as_2523_, size_t v_i_2524_, size_t v_stop_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_usize_dec_eq(v_i_2524_, v_stop_2525_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_array_uget_borrowed(v_as_2523_, v_i_2524_);
lean_inc(v___x_2535_);
lean_inc_ref(v_f_2522_);
v___x_2536_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2522_, v___x_2535_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; size_t v___x_2538_; size_t v___x_2539_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2524_, v___x_2538_);
v_i_2524_ = v___x_2539_;
v_b_2526_ = v_a_2537_;
goto _start;
}
else
{
lean_dec_ref(v_f_2522_);
return v___x_2536_;
}
}
else
{
lean_object* v___x_2541_; 
lean_dec_ref(v_f_2522_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_b_2526_);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2542_, lean_object* v_f_2543_, lean_object* v_as_2544_, lean_object* v_i_2545_, lean_object* v_stop_2546_, lean_object* v_b_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
uint8_t v_pu_boxed_2555_; size_t v_i_boxed_2556_; size_t v_stop_boxed_2557_; lean_object* v_res_2558_; 
v_pu_boxed_2555_ = lean_unbox(v_pu_2542_);
v_i_boxed_2556_ = lean_unbox_usize(v_i_2545_);
lean_dec(v_i_2545_);
v_stop_boxed_2557_ = lean_unbox_usize(v_stop_2546_);
lean_dec(v_stop_2546_);
v_res_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2555_, v_f_2543_, v_as_2544_, v_i_boxed_2556_, v_stop_boxed_2557_, v_b_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v_as_2544_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2559_, lean_object* v_f_2560_, lean_object* v_e_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_args_2570_; 
switch(lean_obj_tag(v_e_2561_))
{
case 2:
{
lean_object* v_struct_2579_; lean_object* v___x_2580_; 
v_struct_2579_ = lean_ctor_get(v_e_2561_, 2);
lean_inc(v_struct_2579_);
lean_dec_ref_known(v_e_2561_, 3);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2580_ = lean_apply_8(v_f_2560_, v_struct_2579_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2580_;
}
case 3:
{
lean_object* v_args_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v_args_2581_ = lean_ctor_get(v_e_2561_, 2);
lean_inc_ref(v_args_2581_);
lean_dec_ref_known(v_e_2561_, 3);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_array_get_size(v_args_2581_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_nat_dec_lt(v___x_2582_, v___x_2583_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
lean_dec_ref(v_args_2581_);
lean_dec_ref(v_f_2560_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
return v___x_2586_;
}
else
{
size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = lean_usize_of_nat(v___x_2583_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2559_, v_f_2560_, v_args_2581_, v___x_2587_, v___x_2588_, v___x_2584_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v_args_2581_);
return v___x_2589_;
}
}
case 4:
{
lean_object* v_fvarId_2590_; lean_object* v_args_2591_; lean_object* v___x_2592_; 
v_fvarId_2590_ = lean_ctor_get(v_e_2561_, 0);
lean_inc(v_fvarId_2590_);
v_args_2591_ = lean_ctor_get(v_e_2561_, 1);
lean_inc_ref(v_args_2591_);
lean_dec_ref_known(v_e_2561_, 2);
lean_inc_ref(v_f_2560_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2592_ = lean_apply_8(v_f_2560_, v_fvarId_2590_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2606_; 
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v___x_2592_, 0);
lean_dec(v_unused_2607_);
v___x_2594_ = v___x_2592_;
v_isShared_2595_ = v_isSharedCheck_2606_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v___x_2592_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2606_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_array_get_size(v_args_2591_);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_nat_dec_lt(v___x_2596_, v___x_2597_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2601_; 
lean_dec_ref(v_args_2591_);
lean_dec_ref(v_f_2560_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2598_);
v___x_2601_ = v___x_2594_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2598_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
lean_del_object(v___x_2594_);
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = lean_usize_of_nat(v___x_2597_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2559_, v_f_2560_, v_args_2591_, v___x_2603_, v___x_2604_, v___x_2598_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v_args_2591_);
return v___x_2605_;
}
}
}
else
{
lean_dec_ref(v_args_2591_);
lean_dec_ref(v_f_2560_);
return v___x_2592_;
}
}
case 5:
{
lean_object* v_args_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_args_2608_ = lean_ctor_get(v_e_2561_, 1);
lean_inc_ref(v_args_2608_);
lean_dec_ref_known(v_e_2561_, 2);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_array_get_size(v_args_2608_);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_nat_dec_lt(v___x_2609_, v___x_2610_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec_ref(v_args_2608_);
lean_dec_ref(v_f_2560_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
return v___x_2613_;
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2610_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2559_, v_f_2560_, v_args_2608_, v___x_2614_, v___x_2615_, v___x_2611_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v_args_2608_);
return v___x_2616_;
}
}
case 6:
{
lean_object* v_var_2617_; lean_object* v___x_2618_; 
v_var_2617_ = lean_ctor_get(v_e_2561_, 1);
lean_inc(v_var_2617_);
lean_dec_ref_known(v_e_2561_, 2);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2618_ = lean_apply_8(v_f_2560_, v_var_2617_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2618_;
}
case 7:
{
lean_object* v_var_2619_; lean_object* v___x_2620_; 
v_var_2619_ = lean_ctor_get(v_e_2561_, 1);
lean_inc(v_var_2619_);
lean_dec_ref_known(v_e_2561_, 2);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2620_ = lean_apply_8(v_f_2560_, v_var_2619_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2620_;
}
case 8:
{
lean_object* v_var_2621_; lean_object* v___x_2622_; 
v_var_2621_ = lean_ctor_get(v_e_2561_, 2);
lean_inc(v_var_2621_);
lean_dec_ref_known(v_e_2561_, 3);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2622_ = lean_apply_8(v_f_2560_, v_var_2621_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2622_;
}
case 9:
{
lean_object* v_args_2623_; 
v_args_2623_ = lean_ctor_get(v_e_2561_, 1);
lean_inc_ref(v_args_2623_);
lean_dec_ref_known(v_e_2561_, 2);
v_args_2570_ = v_args_2623_;
goto v___jp_2569_;
}
case 10:
{
lean_object* v_args_2624_; 
v_args_2624_ = lean_ctor_get(v_e_2561_, 1);
lean_inc_ref(v_args_2624_);
lean_dec_ref_known(v_e_2561_, 2);
v_args_2570_ = v_args_2624_;
goto v___jp_2569_;
}
case 11:
{
lean_object* v_var_2625_; lean_object* v___x_2626_; 
v_var_2625_ = lean_ctor_get(v_e_2561_, 1);
lean_inc(v_var_2625_);
lean_dec_ref_known(v_e_2561_, 2);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2626_ = lean_apply_8(v_f_2560_, v_var_2625_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2626_;
}
case 12:
{
lean_object* v_var_2627_; lean_object* v_args_2628_; lean_object* v___x_2629_; 
v_var_2627_ = lean_ctor_get(v_e_2561_, 0);
lean_inc(v_var_2627_);
v_args_2628_ = lean_ctor_get(v_e_2561_, 2);
lean_inc_ref(v_args_2628_);
lean_dec_ref_known(v_e_2561_, 3);
lean_inc_ref(v_f_2560_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2629_ = lean_apply_8(v_f_2560_, v_var_2627_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2643_; 
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2629_, 0);
lean_dec(v_unused_2644_);
v___x_2631_ = v___x_2629_;
v_isShared_2632_ = v_isSharedCheck_2643_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v___x_2629_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2643_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_array_get_size(v_args_2628_);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_nat_dec_lt(v___x_2633_, v___x_2634_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v_args_2628_);
lean_dec_ref(v_f_2560_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2635_);
v___x_2638_ = v___x_2631_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2635_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; 
lean_del_object(v___x_2631_);
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2634_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2559_, v_f_2560_, v_args_2628_, v___x_2640_, v___x_2641_, v___x_2635_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v_args_2628_);
return v___x_2642_;
}
}
}
else
{
lean_dec_ref(v_args_2628_);
lean_dec_ref(v_f_2560_);
return v___x_2629_;
}
}
case 13:
{
lean_object* v_fvarId_2645_; lean_object* v___x_2646_; 
v_fvarId_2645_ = lean_ctor_get(v_e_2561_, 1);
lean_inc(v_fvarId_2645_);
lean_dec_ref_known(v_e_2561_, 2);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2646_ = lean_apply_8(v_f_2560_, v_fvarId_2645_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2646_;
}
case 14:
{
lean_object* v_fvarId_2647_; lean_object* v___x_2648_; 
v_fvarId_2647_ = lean_ctor_get(v_e_2561_, 0);
lean_inc(v_fvarId_2647_);
lean_dec_ref_known(v_e_2561_, 1);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2648_ = lean_apply_8(v_f_2560_, v_fvarId_2647_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2648_;
}
case 15:
{
lean_object* v_fvarId_2649_; lean_object* v___x_2650_; 
v_fvarId_2649_ = lean_ctor_get(v_e_2561_, 0);
lean_inc(v_fvarId_2649_);
lean_dec_ref_known(v_e_2561_, 1);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v___y_2562_);
v___x_2650_ = lean_apply_8(v_f_2560_, v_fvarId_2649_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, lean_box(0));
return v___x_2650_;
}
default: 
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v_e_2561_);
lean_dec_ref(v_f_2560_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
return v___x_2652_;
}
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_array_get_size(v_args_2570_);
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_dec_ref(v_args_2570_);
lean_dec_ref(v_f_2560_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
return v___x_2575_;
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = lean_usize_of_nat(v___x_2572_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2559_, v_f_2560_, v_args_2570_, v___x_2576_, v___x_2577_, v___x_2573_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v_args_2570_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2653_, lean_object* v_f_2654_, lean_object* v_e_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_pu_boxed_2663_; lean_object* v_res_2664_; 
v_pu_boxed_2663_ = lean_unbox(v_pu_2653_);
v_res_2664_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2663_, v_f_2654_, v_e_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2665_, lean_object* v_f_2666_, lean_object* v_decl_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_type_2675_; lean_object* v_value_2676_; lean_object* v___x_2677_; 
v_type_2675_ = lean_ctor_get(v_decl_2667_, 2);
lean_inc_ref(v_type_2675_);
v_value_2676_ = lean_ctor_get(v_decl_2667_, 3);
lean_inc(v_value_2676_);
lean_dec_ref(v_decl_2667_);
lean_inc_ref(v_f_2666_);
v___x_2677_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2666_, v_type_2675_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref_known(v___x_2677_, 1);
v___x_2678_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2665_, v_f_2666_, v_value_2676_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2678_;
}
else
{
lean_dec(v_value_2676_);
lean_dec_ref(v_f_2666_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2679_, lean_object* v_f_2680_, lean_object* v_decl_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v_pu_boxed_2689_; lean_object* v_res_2690_; 
v_pu_boxed_2689_ = lean_unbox(v_pu_2679_);
v_res_2690_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2689_, v_f_2680_, v_decl_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec(v___y_2682_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2691_, lean_object* v_f_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
switch(lean_obj_tag(v_alt_2691_))
{
case 0:
{
lean_object* v_code_2700_; lean_object* v___x_2701_; 
v_code_2700_ = lean_ctor_get(v_alt_2691_, 2);
lean_inc_ref(v_code_2700_);
lean_dec_ref_known(v_alt_2691_, 3);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc(v___y_2693_);
v___x_2701_ = lean_apply_8(v_f_2692_, v_code_2700_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
return v___x_2701_;
}
case 1:
{
lean_object* v_code_2702_; lean_object* v___x_2703_; 
v_code_2702_ = lean_ctor_get(v_alt_2691_, 1);
lean_inc_ref(v_code_2702_);
lean_dec_ref_known(v_alt_2691_, 2);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc(v___y_2693_);
v___x_2703_ = lean_apply_8(v_f_2692_, v_code_2702_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
return v___x_2703_;
}
default: 
{
lean_object* v_code_2704_; lean_object* v___x_2705_; 
v_code_2704_ = lean_ctor_get(v_alt_2691_, 0);
lean_inc_ref(v_code_2704_);
lean_dec_ref_known(v_alt_2691_, 1);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc(v___y_2693_);
v___x_2705_ = lean_apply_8(v_f_2692_, v_code_2704_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2706_, lean_object* v_f_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2706_, v_f_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2716_, lean_object* v_f_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v_pu_boxed_2726_; lean_object* v_res_2727_; 
v_pu_boxed_2726_ = lean_unbox(v_pu_2716_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2726_, v_f_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2728_, lean_object* v_f_2729_, lean_object* v_as_2730_, size_t v_i_2731_, size_t v_stop_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_eq(v_i_2731_, v_stop_2732_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2742_ = lean_box(v_pu_2728_);
lean_inc_ref(v_f_2729_);
v___f_2743_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2743_, 0, v___x_2742_);
lean_closure_set(v___f_2743_, 1, v_f_2729_);
v___x_2744_ = lean_array_uget_borrowed(v_as_2730_, v_i_2731_);
lean_inc(v___x_2744_);
v___x_2745_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2744_, v___f_2743_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; size_t v___x_2747_; size_t v___x_2748_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = ((size_t)1ULL);
v___x_2748_ = lean_usize_add(v_i_2731_, v___x_2747_);
v_i_2731_ = v___x_2748_;
v_b_2733_ = v_a_2746_;
goto _start;
}
else
{
lean_dec_ref(v_f_2729_);
return v___x_2745_;
}
}
else
{
lean_object* v___x_2750_; 
lean_dec_ref(v_f_2729_);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_b_2733_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2751_, lean_object* v_f_2752_, lean_object* v_c_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
switch(lean_obj_tag(v_c_2753_))
{
case 0:
{
lean_object* v_decl_2761_; lean_object* v_k_2762_; lean_object* v___x_2763_; 
v_decl_2761_ = lean_ctor_get(v_c_2753_, 0);
lean_inc_ref(v_decl_2761_);
v_k_2762_ = lean_ctor_get(v_c_2753_, 1);
lean_inc_ref(v_k_2762_);
lean_dec_ref_known(v_c_2753_, 2);
lean_inc_ref(v_f_2752_);
v___x_2763_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2751_, v_f_2752_, v_decl_2761_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_dec_ref_known(v___x_2763_, 1);
v_c_2753_ = v_k_2762_;
goto _start;
}
else
{
lean_dec_ref(v_k_2762_);
lean_dec_ref(v_f_2752_);
return v___x_2763_;
}
}
case 3:
{
lean_object* v_fvarId_2765_; lean_object* v_args_2766_; lean_object* v___x_2767_; 
v_fvarId_2765_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2765_);
v_args_2766_ = lean_ctor_get(v_c_2753_, 1);
lean_inc_ref(v_args_2766_);
lean_dec_ref_known(v_c_2753_, 2);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2767_ = lean_apply_8(v_f_2752_, v_fvarId_2765_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2781_; 
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v___x_2767_, 0);
lean_dec(v_unused_2782_);
v___x_2769_ = v___x_2767_;
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
else
{
lean_dec(v___x_2767_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_array_get_size(v_args_2766_);
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_nat_dec_lt(v___x_2771_, v___x_2772_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_dec_ref(v_args_2766_);
lean_dec_ref(v_f_2752_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2773_);
v___x_2776_ = v___x_2769_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2773_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
lean_del_object(v___x_2769_);
v___x_2778_ = ((size_t)0ULL);
v___x_2779_ = lean_usize_of_nat(v___x_2772_);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2751_, v_f_2752_, v_args_2766_, v___x_2778_, v___x_2779_, v___x_2773_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec_ref(v_args_2766_);
return v___x_2780_;
}
}
}
else
{
lean_dec_ref(v_args_2766_);
lean_dec_ref(v_f_2752_);
return v___x_2767_;
}
}
case 4:
{
lean_object* v_cases_2783_; lean_object* v_resultType_2784_; lean_object* v_discr_2785_; lean_object* v_alts_2786_; lean_object* v___x_2787_; 
v_cases_2783_ = lean_ctor_get(v_c_2753_, 0);
lean_inc_ref(v_cases_2783_);
lean_dec_ref_known(v_c_2753_, 1);
v_resultType_2784_ = lean_ctor_get(v_cases_2783_, 1);
lean_inc_ref(v_resultType_2784_);
v_discr_2785_ = lean_ctor_get(v_cases_2783_, 2);
lean_inc(v_discr_2785_);
v_alts_2786_ = lean_ctor_get(v_cases_2783_, 3);
lean_inc_ref(v_alts_2786_);
lean_dec_ref(v_cases_2783_);
lean_inc_ref(v_f_2752_);
v___x_2787_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2752_, v_resultType_2784_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; 
lean_dec_ref_known(v___x_2787_, 1);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2788_ = lean_apply_8(v_f_2752_, v_discr_2785_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2802_; 
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2788_, 0);
lean_dec(v_unused_2803_);
v___x_2790_ = v___x_2788_;
v_isShared_2791_ = v_isSharedCheck_2802_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v___x_2788_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2802_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = lean_array_get_size(v_alts_2786_);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_nat_dec_lt(v___x_2792_, v___x_2793_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2797_; 
lean_dec_ref(v_alts_2786_);
lean_dec_ref(v_f_2752_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2794_);
v___x_2797_ = v___x_2790_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2794_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
else
{
size_t v___x_2799_; size_t v___x_2800_; lean_object* v___x_2801_; 
lean_del_object(v___x_2790_);
v___x_2799_ = ((size_t)0ULL);
v___x_2800_ = lean_usize_of_nat(v___x_2793_);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2751_, v_f_2752_, v_alts_2786_, v___x_2799_, v___x_2800_, v___x_2794_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec_ref(v_alts_2786_);
return v___x_2801_;
}
}
}
else
{
lean_dec_ref(v_alts_2786_);
lean_dec_ref(v_f_2752_);
return v___x_2788_;
}
}
else
{
lean_dec_ref(v_alts_2786_);
lean_dec(v_discr_2785_);
lean_dec_ref(v_f_2752_);
return v___x_2787_;
}
}
case 5:
{
lean_object* v_fvarId_2804_; lean_object* v___x_2805_; 
v_fvarId_2804_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2804_);
lean_dec_ref_known(v_c_2753_, 1);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2805_ = lean_apply_8(v_f_2752_, v_fvarId_2804_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
return v___x_2805_;
}
case 6:
{
lean_object* v_type_2806_; lean_object* v___x_2807_; 
v_type_2806_ = lean_ctor_get(v_c_2753_, 0);
lean_inc_ref(v_type_2806_);
lean_dec_ref_known(v_c_2753_, 1);
v___x_2807_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2752_, v_type_2806_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2807_;
}
case 7:
{
lean_object* v_fvarId_2808_; lean_object* v_y_2809_; lean_object* v_k_2810_; lean_object* v___x_2811_; 
v_fvarId_2808_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2808_);
v_y_2809_ = lean_ctor_get(v_c_2753_, 2);
lean_inc(v_y_2809_);
v_k_2810_ = lean_ctor_get(v_c_2753_, 3);
lean_inc_ref(v_k_2810_);
lean_dec_ref_known(v_c_2753_, 4);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2811_ = lean_apply_8(v_f_2752_, v_fvarId_2808_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref_known(v___x_2811_, 1);
lean_inc_ref(v_f_2752_);
v___x_2812_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2752_, v_y_2809_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_dec_ref_known(v___x_2812_, 1);
v_c_2753_ = v_k_2810_;
goto _start;
}
else
{
lean_dec_ref(v_k_2810_);
lean_dec_ref(v_f_2752_);
return v___x_2812_;
}
}
else
{
lean_dec_ref(v_k_2810_);
lean_dec(v_y_2809_);
lean_dec_ref(v_f_2752_);
return v___x_2811_;
}
}
case 8:
{
lean_object* v_fvarId_2814_; lean_object* v_y_2815_; lean_object* v_k_2816_; lean_object* v___x_2817_; 
v_fvarId_2814_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2814_);
v_y_2815_ = lean_ctor_get(v_c_2753_, 2);
lean_inc(v_y_2815_);
v_k_2816_ = lean_ctor_get(v_c_2753_, 3);
lean_inc_ref(v_k_2816_);
lean_dec_ref_known(v_c_2753_, 4);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2817_ = lean_apply_8(v_f_2752_, v_fvarId_2814_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v___x_2818_; 
lean_dec_ref_known(v___x_2817_, 1);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2818_ = lean_apply_8(v_f_2752_, v_y_2815_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_dec_ref_known(v___x_2818_, 1);
v_c_2753_ = v_k_2816_;
goto _start;
}
else
{
lean_dec_ref(v_k_2816_);
lean_dec_ref(v_f_2752_);
return v___x_2818_;
}
}
else
{
lean_dec_ref(v_k_2816_);
lean_dec(v_y_2815_);
lean_dec_ref(v_f_2752_);
return v___x_2817_;
}
}
case 9:
{
lean_object* v_fvarId_2820_; lean_object* v_y_2821_; lean_object* v_ty_2822_; lean_object* v_k_2823_; lean_object* v___x_2824_; 
v_fvarId_2820_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2820_);
v_y_2821_ = lean_ctor_get(v_c_2753_, 3);
lean_inc(v_y_2821_);
v_ty_2822_ = lean_ctor_get(v_c_2753_, 4);
lean_inc_ref(v_ty_2822_);
v_k_2823_ = lean_ctor_get(v_c_2753_, 5);
lean_inc_ref(v_k_2823_);
lean_dec_ref_known(v_c_2753_, 6);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2824_ = lean_apply_8(v_f_2752_, v_fvarId_2820_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2825_; 
lean_dec_ref_known(v___x_2824_, 1);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2825_ = lean_apply_8(v_f_2752_, v_y_2821_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2826_; 
lean_dec_ref_known(v___x_2825_, 1);
lean_inc_ref(v_f_2752_);
v___x_2826_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2752_, v_ty_2822_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_dec_ref_known(v___x_2826_, 1);
v_c_2753_ = v_k_2823_;
goto _start;
}
else
{
lean_dec_ref(v_k_2823_);
lean_dec_ref(v_f_2752_);
return v___x_2826_;
}
}
else
{
lean_dec_ref(v_k_2823_);
lean_dec_ref(v_ty_2822_);
lean_dec_ref(v_f_2752_);
return v___x_2825_;
}
}
else
{
lean_dec_ref(v_k_2823_);
lean_dec_ref(v_ty_2822_);
lean_dec(v_y_2821_);
lean_dec_ref(v_f_2752_);
return v___x_2824_;
}
}
case 10:
{
lean_object* v_fvarId_2828_; lean_object* v_k_2829_; lean_object* v___x_2830_; 
v_fvarId_2828_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2828_);
v_k_2829_ = lean_ctor_get(v_c_2753_, 2);
lean_inc_ref(v_k_2829_);
lean_dec_ref_known(v_c_2753_, 3);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2830_ = lean_apply_8(v_f_2752_, v_fvarId_2828_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_dec_ref_known(v___x_2830_, 1);
v_c_2753_ = v_k_2829_;
goto _start;
}
else
{
lean_dec_ref(v_k_2829_);
lean_dec_ref(v_f_2752_);
return v___x_2830_;
}
}
case 11:
{
lean_object* v_fvarId_2832_; lean_object* v_k_2833_; lean_object* v___x_2834_; 
v_fvarId_2832_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2832_);
v_k_2833_ = lean_ctor_get(v_c_2753_, 2);
lean_inc_ref(v_k_2833_);
lean_dec_ref_known(v_c_2753_, 3);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2834_ = lean_apply_8(v_f_2752_, v_fvarId_2832_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_dec_ref_known(v___x_2834_, 1);
v_c_2753_ = v_k_2833_;
goto _start;
}
else
{
lean_dec_ref(v_k_2833_);
lean_dec_ref(v_f_2752_);
return v___x_2834_;
}
}
case 12:
{
lean_object* v_fvarId_2836_; lean_object* v_k_2837_; lean_object* v___x_2838_; 
v_fvarId_2836_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2836_);
v_k_2837_ = lean_ctor_get(v_c_2753_, 3);
lean_inc_ref(v_k_2837_);
lean_dec_ref_known(v_c_2753_, 4);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2838_ = lean_apply_8(v_f_2752_, v_fvarId_2836_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_dec_ref_known(v___x_2838_, 1);
v_c_2753_ = v_k_2837_;
goto _start;
}
else
{
lean_dec_ref(v_k_2837_);
lean_dec_ref(v_f_2752_);
return v___x_2838_;
}
}
case 13:
{
lean_object* v_fvarId_2840_; lean_object* v_k_2841_; lean_object* v___x_2842_; 
v_fvarId_2840_ = lean_ctor_get(v_c_2753_, 0);
lean_inc(v_fvarId_2840_);
v_k_2841_ = lean_ctor_get(v_c_2753_, 1);
lean_inc_ref(v_k_2841_);
lean_dec_ref_known(v_c_2753_, 2);
lean_inc_ref(v_f_2752_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc(v___y_2754_);
v___x_2842_ = lean_apply_8(v_f_2752_, v_fvarId_2840_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref_known(v___x_2842_, 1);
v_c_2753_ = v_k_2841_;
goto _start;
}
else
{
lean_dec_ref(v_k_2841_);
lean_dec_ref(v_f_2752_);
return v___x_2842_;
}
}
default: 
{
lean_object* v_decl_2844_; lean_object* v_k_2845_; lean_object* v_params_2846_; lean_object* v_type_2847_; lean_object* v_value_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_decl_2844_ = lean_ctor_get(v_c_2753_, 0);
lean_inc_ref(v_decl_2844_);
v_k_2845_ = lean_ctor_get(v_c_2753_, 1);
lean_inc_ref(v_k_2845_);
lean_dec_ref(v_c_2753_);
v_params_2846_ = lean_ctor_get(v_decl_2844_, 2);
lean_inc_ref(v_params_2846_);
v_type_2847_ = lean_ctor_get(v_decl_2844_, 3);
lean_inc_ref(v_type_2847_);
v_value_2848_ = lean_ctor_get(v_decl_2844_, 4);
lean_inc_ref(v_value_2848_);
lean_dec_ref(v_decl_2844_);
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_array_get_size(v_params_2846_);
v___x_2851_ = lean_nat_dec_lt(v___x_2849_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec_ref(v_params_2846_);
lean_inc_ref(v_f_2752_);
v___x_2852_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2752_, v_type_2847_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref_known(v___x_2852_, 1);
lean_inc_ref(v_f_2752_);
v___x_2853_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2751_, v_f_2752_, v_value_2848_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref_known(v___x_2853_, 1);
v_c_2753_ = v_k_2845_;
goto _start;
}
else
{
lean_dec_ref(v_k_2845_);
lean_dec_ref(v_f_2752_);
return v___x_2853_;
}
}
else
{
lean_dec_ref(v_value_2848_);
lean_dec_ref(v_k_2845_);
lean_dec_ref(v_f_2752_);
return v___x_2852_;
}
}
else
{
lean_object* v___x_2855_; size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = lean_box(0);
v___x_2856_ = ((size_t)0ULL);
v___x_2857_ = lean_usize_of_nat(v___x_2850_);
lean_inc_ref(v_f_2752_);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2751_, v_f_2752_, v_params_2846_, v___x_2856_, v___x_2857_, v___x_2855_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec_ref(v_params_2846_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v___x_2859_; 
lean_dec_ref_known(v___x_2858_, 1);
lean_inc_ref(v_f_2752_);
v___x_2859_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2752_, v_type_2847_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref_known(v___x_2859_, 1);
lean_inc_ref(v_f_2752_);
v___x_2860_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2751_, v_f_2752_, v_value_2848_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref_known(v___x_2860_, 1);
v_c_2753_ = v_k_2845_;
goto _start;
}
else
{
lean_dec_ref(v_k_2845_);
lean_dec_ref(v_f_2752_);
return v___x_2860_;
}
}
else
{
lean_dec_ref(v_value_2848_);
lean_dec_ref(v_k_2845_);
lean_dec_ref(v_f_2752_);
return v___x_2859_;
}
}
else
{
lean_dec_ref(v_value_2848_);
lean_dec_ref(v_type_2847_);
lean_dec_ref(v_k_2845_);
lean_dec_ref(v_f_2752_);
return v___x_2858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2862_, lean_object* v_f_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2862_, v_f_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_2873_, lean_object* v_f_2874_, lean_object* v_as_2875_, lean_object* v_i_2876_, lean_object* v_stop_2877_, lean_object* v_b_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_pu_boxed_2886_; size_t v_i_boxed_2887_; size_t v_stop_boxed_2888_; lean_object* v_res_2889_; 
v_pu_boxed_2886_ = lean_unbox(v_pu_2873_);
v_i_boxed_2887_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_stop_boxed_2888_ = lean_unbox_usize(v_stop_2877_);
lean_dec(v_stop_2877_);
v_res_2889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_2886_, v_f_2874_, v_as_2875_, v_i_boxed_2887_, v_stop_boxed_2888_, v_b_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v_as_2875_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_2890_, lean_object* v_f_2891_, lean_object* v_c_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
uint8_t v_pu_boxed_2900_; lean_object* v_res_2901_; 
v_pu_boxed_2900_ = lean_unbox(v_pu_2890_);
v_res_2901_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_2900_, v_f_2891_, v_c_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec(v___y_2893_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_2902_, lean_object* v_f_2903_, lean_object* v_decl_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_params_2912_; lean_object* v_type_2913_; lean_object* v_value_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_params_2912_ = lean_ctor_get(v_decl_2904_, 2);
lean_inc_ref(v_params_2912_);
v_type_2913_ = lean_ctor_get(v_decl_2904_, 3);
lean_inc_ref(v_type_2913_);
v_value_2914_ = lean_ctor_get(v_decl_2904_, 4);
lean_inc_ref(v_value_2914_);
lean_dec_ref(v_decl_2904_);
v___x_2915_ = lean_unsigned_to_nat(0u);
v___x_2916_ = lean_array_get_size(v_params_2912_);
v___x_2917_ = lean_nat_dec_lt(v___x_2915_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; 
lean_dec_ref(v_params_2912_);
lean_inc_ref(v_f_2903_);
v___x_2918_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2903_, v_type_2913_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v___x_2919_; 
lean_dec_ref_known(v___x_2918_, 1);
v___x_2919_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2902_, v_f_2903_, v_value_2914_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2919_;
}
else
{
lean_dec_ref(v_value_2914_);
lean_dec_ref(v_f_2903_);
return v___x_2918_;
}
}
else
{
lean_object* v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v___x_2920_ = lean_box(0);
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = lean_usize_of_nat(v___x_2916_);
lean_inc_ref(v_f_2903_);
v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2902_, v_f_2903_, v_params_2912_, v___x_2921_, v___x_2922_, v___x_2920_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec_ref(v_params_2912_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v___x_2924_; 
lean_dec_ref_known(v___x_2923_, 1);
lean_inc_ref(v_f_2903_);
v___x_2924_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2903_, v_type_2913_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2925_; 
lean_dec_ref_known(v___x_2924_, 1);
v___x_2925_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2902_, v_f_2903_, v_value_2914_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2925_;
}
else
{
lean_dec_ref(v_value_2914_);
lean_dec_ref(v_f_2903_);
return v___x_2924_;
}
}
else
{
lean_dec_ref(v_value_2914_);
lean_dec_ref(v_type_2913_);
lean_dec_ref(v_f_2903_);
return v___x_2923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_2926_, lean_object* v_f_2927_, lean_object* v_decl_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_pu_boxed_2936_; lean_object* v_res_2937_; 
v_pu_boxed_2936_ = lean_unbox(v_pu_2926_);
v_res_2937_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_2936_, v_f_2927_, v_decl_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_box(0);
v___x_2940_ = lean_panic_fn_borrowed(v___x_2939_, v_msg_2938_);
return v___x_2940_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2944_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_2945_ = lean_unsigned_to_nat(11u);
v___x_2946_ = lean_unsigned_to_nat(163u);
v___x_2947_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_2948_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_2949_ = l_mkPanicMessageWithDecl(v___x_2948_, v___x_2947_, v___x_2946_, v___x_2945_, v___x_2944_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_2950_, lean_object* v_x_2951_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_2953_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_2952_);
return v___x_2953_;
}
else
{
lean_object* v_key_2954_; lean_object* v_value_2955_; lean_object* v_tail_2956_; uint8_t v___x_2957_; 
v_key_2954_ = lean_ctor_get(v_x_2951_, 0);
v_value_2955_ = lean_ctor_get(v_x_2951_, 1);
v_tail_2956_ = lean_ctor_get(v_x_2951_, 2);
v___x_2957_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2954_, v_a_2950_);
if (v___x_2957_ == 0)
{
v_x_2951_ = v_tail_2956_;
goto _start;
}
else
{
lean_inc(v_value_2955_);
return v_value_2955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_2959_, lean_object* v_x_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_2959_, v_x_2960_);
lean_dec(v_x_2960_);
lean_dec(v_a_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_buckets_2964_; lean_object* v___x_2965_; uint64_t v___x_2966_; uint64_t v___x_2967_; uint64_t v___x_2968_; uint64_t v_fold_2969_; uint64_t v___x_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_buckets_2964_ = lean_ctor_get(v_m_2962_, 1);
v___x_2965_ = lean_array_get_size(v_buckets_2964_);
v___x_2966_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2963_);
v___x_2967_ = 32ULL;
v___x_2968_ = lean_uint64_shift_right(v___x_2966_, v___x_2967_);
v_fold_2969_ = lean_uint64_xor(v___x_2966_, v___x_2968_);
v___x_2970_ = 16ULL;
v___x_2971_ = lean_uint64_shift_right(v_fold_2969_, v___x_2970_);
v___x_2972_ = lean_uint64_xor(v_fold_2969_, v___x_2971_);
v___x_2973_ = lean_uint64_to_usize(v___x_2972_);
v___x_2974_ = lean_usize_of_nat(v___x_2965_);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_sub(v___x_2974_, v___x_2975_);
v___x_2977_ = lean_usize_land(v___x_2973_, v___x_2976_);
v___x_2978_ = lean_array_uget_borrowed(v_buckets_2964_, v___x_2977_);
v___x_2979_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_2963_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_m_2980_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___y_2993_; uint8_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = 0;
v___x_3019_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_2984_))
{
case 0:
{
lean_object* v_decl_3020_; lean_object* v___x_3021_; 
v_decl_3020_ = lean_ctor_get(v_decl_2984_, 0);
lean_inc_ref(v_decl_3020_);
v___x_3021_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3018_, v___x_3019_, v_decl_3020_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
v___y_2993_ = v___x_3021_;
goto v___jp_2992_;
}
case 1:
{
lean_object* v_decl_3022_; lean_object* v___x_3023_; 
v_decl_3022_ = lean_ctor_get(v_decl_2984_, 0);
lean_inc_ref(v_decl_3022_);
v___x_3023_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3018_, v___x_3019_, v_decl_3022_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
v___y_2993_ = v___x_3023_;
goto v___jp_2992_;
}
case 2:
{
lean_object* v_decl_3024_; lean_object* v___x_3025_; 
v_decl_3024_ = lean_ctor_get(v_decl_2984_, 0);
lean_inc_ref(v_decl_3024_);
v___x_3025_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3018_, v___x_3019_, v_decl_3024_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
v___y_2993_ = v___x_3025_;
goto v___jp_2992_;
}
case 3:
{
lean_object* v_fvarId_3026_; lean_object* v_y_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v_fvarId_3026_ = lean_ctor_get(v_decl_2984_, 0);
v_y_3027_ = lean_ctor_get(v_decl_2984_, 2);
lean_inc(v_fvarId_3026_);
v___x_3028_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3026_, v_a_2985_);
lean_dec_ref(v___x_3028_);
lean_inc(v_y_3027_);
v___x_3029_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3019_, v_y_3027_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
v___y_2993_ = v___x_3029_;
goto v___jp_2992_;
}
case 4:
{
lean_object* v_fvarId_3030_; lean_object* v_y_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_fvarId_3030_ = lean_ctor_get(v_decl_2984_, 0);
v_y_3031_ = lean_ctor_get(v_decl_2984_, 2);
lean_inc(v_fvarId_3030_);
v___x_3032_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3030_, v_a_2985_);
lean_dec_ref(v___x_3032_);
lean_inc(v_y_3031_);
v___x_3033_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3031_, v_a_2985_);
v___y_2993_ = v___x_3033_;
goto v___jp_2992_;
}
case 5:
{
lean_object* v_fvarId_3034_; lean_object* v_y_3035_; lean_object* v_ty_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v_fvarId_3034_ = lean_ctor_get(v_decl_2984_, 0);
v_y_3035_ = lean_ctor_get(v_decl_2984_, 3);
v_ty_3036_ = lean_ctor_get(v_decl_2984_, 4);
lean_inc(v_fvarId_3034_);
v___x_3037_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3034_, v_a_2985_);
lean_dec_ref(v___x_3037_);
lean_inc(v_y_3035_);
v___x_3038_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3035_, v_a_2985_);
lean_dec_ref(v___x_3038_);
lean_inc_ref(v_ty_3036_);
v___x_3039_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3019_, v_ty_3036_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
v___y_2993_ = v___x_3039_;
goto v___jp_2992_;
}
default: 
{
lean_object* v_fvarId_3040_; lean_object* v___x_3041_; 
v_fvarId_3040_ = lean_ctor_get(v_decl_2984_, 0);
lean_inc(v_fvarId_3040_);
v___x_3041_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3040_, v_a_2985_);
v___y_2993_ = v___x_3041_;
goto v___jp_2992_;
}
}
v___jp_2992_:
{
if (lean_obj_tag(v___y_2993_) == 0)
{
lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3016_; 
v_isSharedCheck_3016_ = !lean_is_exclusive(v___y_2993_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___y_2993_, 0);
lean_dec(v_unused_3017_);
v___x_2995_ = v___y_2993_;
v_isShared_2996_ = v_isSharedCheck_3016_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v___y_2993_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3016_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v_decision_2998_; lean_object* v_newArms_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3015_; 
v___x_2997_ = lean_st_ref_take(v_a_2985_);
v_decision_2998_ = lean_ctor_get(v___x_2997_, 0);
v_newArms_2999_ = lean_ctor_get(v___x_2997_, 1);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3001_ = v___x_2997_;
v_isShared_3002_ = v_isSharedCheck_3015_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_newArms_2999_);
lean_inc(v_decision_2998_);
lean_dec(v___x_2997_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3015_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_box(2);
v___x_3005_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_2999_, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_decl_2984_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_2999_, v___x_3004_, v___x_3006_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3007_);
v___x_3009_ = v___x_3001_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_decision_2998_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = lean_st_ref_put(v_a_2985_, v___x_3009_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_3003_);
v___x_3012_ = v___x_2995_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3003_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2984_);
return v___y_2993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec(v_a_3043_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3051_, lean_object* v_f_3052_, lean_object* v_arg_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3052_, v_arg_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3062_, lean_object* v_f_3063_, lean_object* v_arg_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
uint8_t v_pu_boxed_3072_; lean_object* v_res_3073_; 
v_pu_boxed_3072_ = lean_unbox(v_pu_3062_);
v_res_3073_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3072_, v_f_3063_, v_arg_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec(v___y_3065_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3074_, lean_object* v_f_3075_, lean_object* v_param_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3075_, v_param_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3085_, lean_object* v_f_3086_, lean_object* v_param_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
uint8_t v_pu_boxed_3095_; lean_object* v_res_3096_; 
v_pu_boxed_3095_ = lean_unbox(v_pu_3085_);
v_res_3096_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3095_, v_f_3086_, v_param_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec(v___y_3088_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3097_, lean_object* v_alt_3098_, lean_object* v_f_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3098_, v_f_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3108_, lean_object* v_alt_3109_, lean_object* v_f_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v_pu_boxed_3118_; lean_object* v_res_3119_; 
v_pu_boxed_3118_ = lean_unbox(v_pu_3108_);
v_res_3119_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3118_, v_alt_3109_, v_f_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec(v___y_3111_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3120_, lean_object* v_arm_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3124_; lean_object* v_decision_3125_; lean_object* v___x_3126_; 
v___x_3124_ = lean_st_ref_get(v_a_3122_);
v_decision_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc_ref(v_decision_3125_);
lean_dec(v___x_3124_);
v___x_3126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3125_, v_fvar_3120_);
lean_dec_ref(v_decision_3125_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3171_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3171_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_val_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3171_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3131_ = lean_box(3);
v___x_3132_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3127_, v___x_3131_);
if (v___x_3132_ == 0)
{
uint8_t v___x_3133_; 
v___x_3133_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3127_, v_arm_3121_);
lean_dec(v_arm_3121_);
lean_dec(v_val_3127_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v_decision_3135_; lean_object* v_newArms_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3150_; 
v___x_3134_ = lean_st_ref_take(v_a_3122_);
v_decision_3135_ = lean_ctor_get(v___x_3134_, 0);
v_newArms_3136_ = lean_ctor_get(v___x_3134_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3138_ = v___x_3134_;
v_isShared_3139_ = v_isSharedCheck_3150_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_newArms_3136_);
lean_inc(v_decision_3135_);
lean_dec(v___x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3150_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3140_ = lean_box(0);
v___x_3141_ = lean_box(2);
v___x_3142_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3135_, v_fvar_3120_, v___x_3141_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3142_);
v___x_3144_ = v___x_3138_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_newArms_3136_);
v___x_3144_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_st_ref_put(v_a_3122_, v___x_3144_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3140_);
v___x_3147_ = v___x_3129_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3140_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_dec(v_fvar_3120_);
v___x_3151_ = lean_box(0);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3151_);
v___x_3153_ = v___x_3129_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
else
{
lean_object* v___x_3155_; lean_object* v_decision_3156_; lean_object* v_newArms_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_val_3127_);
v___x_3155_ = lean_st_ref_take(v_a_3122_);
v_decision_3156_ = lean_ctor_get(v___x_3155_, 0);
v_newArms_3157_ = lean_ctor_get(v___x_3155_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3159_ = v___x_3155_;
v_isShared_3160_ = v_isSharedCheck_3170_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_newArms_3157_);
lean_inc(v_decision_3156_);
lean_dec(v___x_3155_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3170_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3161_ = lean_box(0);
v___x_3162_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3156_, v_fvar_3120_, v_arm_3121_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3162_);
v___x_3164_ = v___x_3159_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_newArms_3157_);
v___x_3164_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_st_ref_put(v_a_3122_, v___x_3164_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3161_);
v___x_3167_ = v___x_3129_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3161_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec(v___x_3126_);
lean_dec(v_arm_3121_);
lean_dec(v_fvar_3120_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3174_, lean_object* v_arm_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3174_, v_arm_3175_, v_a_3176_);
lean_dec(v_a_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3179_, lean_object* v_arm_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3179_, v_arm_3180_, v_a_3181_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3189_, lean_object* v_arm_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3189_, v_arm_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec(v_a_3191_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3200_, v___x_3199_, v___y_3201_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3209_, v_x_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec(v___y_3211_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3219_){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3221_ = lean_panic_fn_borrowed(v___x_3220_, v_msg_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3222_, lean_object* v_x_3223_){
_start:
{
if (lean_obj_tag(v_x_3223_) == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3225_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3224_);
return v___x_3225_;
}
else
{
lean_object* v_key_3226_; lean_object* v_value_3227_; lean_object* v_tail_3228_; uint8_t v___x_3229_; 
v_key_3226_ = lean_ctor_get(v_x_3223_, 0);
v_value_3227_ = lean_ctor_get(v_x_3223_, 1);
v_tail_3228_ = lean_ctor_get(v_x_3223_, 2);
v___x_3229_ = l_Lean_instBEqFVarId_beq(v_key_3226_, v_a_3222_);
if (v___x_3229_ == 0)
{
v_x_3223_ = v_tail_3228_;
goto _start;
}
else
{
lean_inc(v_value_3227_);
return v_value_3227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3231_, v_x_3232_);
lean_dec(v_x_3232_);
lean_dec(v_a_3231_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v_buckets_3236_; lean_object* v___x_3237_; uint64_t v___x_3238_; uint64_t v___x_3239_; uint64_t v___x_3240_; uint64_t v_fold_3241_; uint64_t v___x_3242_; uint64_t v___x_3243_; uint64_t v___x_3244_; size_t v___x_3245_; size_t v___x_3246_; size_t v___x_3247_; size_t v___x_3248_; size_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_buckets_3236_ = lean_ctor_get(v_m_3234_, 1);
v___x_3237_ = lean_array_get_size(v_buckets_3236_);
v___x_3238_ = l_Lean_instHashableFVarId_hash(v_a_3235_);
v___x_3239_ = 32ULL;
v___x_3240_ = lean_uint64_shift_right(v___x_3238_, v___x_3239_);
v_fold_3241_ = lean_uint64_xor(v___x_3238_, v___x_3240_);
v___x_3242_ = 16ULL;
v___x_3243_ = lean_uint64_shift_right(v_fold_3241_, v___x_3242_);
v___x_3244_ = lean_uint64_xor(v_fold_3241_, v___x_3243_);
v___x_3245_ = lean_uint64_to_usize(v___x_3244_);
v___x_3246_ = lean_usize_of_nat(v___x_3237_);
v___x_3247_ = ((size_t)1ULL);
v___x_3248_ = lean_usize_sub(v___x_3246_, v___x_3247_);
v___x_3249_ = lean_usize_land(v___x_3245_, v___x_3248_);
v___x_3250_ = lean_array_uget_borrowed(v_buckets_3236_, v___x_3249_);
v___x_3251_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3235_, v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_m_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v_decision_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3321_; 
v___x_3263_ = lean_st_ref_get(v_a_3256_);
v_decision_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v___x_3263_, 1);
lean_dec(v_unused_3322_);
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3321_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_decision_3264_);
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3321_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
uint8_t v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___y_3272_; lean_object* v___f_3298_; 
v___x_3268_ = 0;
v___x_3269_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3255_);
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3264_, v___x_3269_);
lean_dec(v___x_3269_);
lean_dec_ref(v_decision_3264_);
lean_inc(v___x_3270_);
v___f_3298_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3298_, 0, v___x_3270_);
switch(lean_obj_tag(v_decl_3255_))
{
case 0:
{
lean_object* v_decl_3299_; lean_object* v___x_3300_; 
v_decl_3299_ = lean_ctor_get(v_decl_3255_, 0);
lean_inc_ref(v_decl_3299_);
v___x_3300_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3268_, v___f_3298_, v_decl_3299_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
v___y_3272_ = v___x_3300_;
goto v___jp_3271_;
}
case 1:
{
lean_object* v_decl_3301_; lean_object* v___x_3302_; 
v_decl_3301_ = lean_ctor_get(v_decl_3255_, 0);
lean_inc_ref(v_decl_3301_);
v___x_3302_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3268_, v___f_3298_, v_decl_3301_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
v___y_3272_ = v___x_3302_;
goto v___jp_3271_;
}
case 2:
{
lean_object* v_decl_3303_; lean_object* v___x_3304_; 
v_decl_3303_ = lean_ctor_get(v_decl_3255_, 0);
lean_inc_ref(v_decl_3303_);
v___x_3304_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3268_, v___f_3298_, v_decl_3303_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
v___y_3272_ = v___x_3304_;
goto v___jp_3271_;
}
case 3:
{
lean_object* v_fvarId_3305_; lean_object* v_y_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_fvarId_3305_ = lean_ctor_get(v_decl_3255_, 0);
v_y_3306_ = lean_ctor_get(v_decl_3255_, 2);
lean_inc(v___x_3270_);
lean_inc(v_fvarId_3305_);
v___x_3307_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3305_, v___x_3270_, v_a_3256_);
lean_dec_ref(v___x_3307_);
lean_inc(v_y_3306_);
v___x_3308_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3298_, v_y_3306_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
v___y_3272_ = v___x_3308_;
goto v___jp_3271_;
}
case 4:
{
lean_object* v_fvarId_3309_; lean_object* v_y_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_dec_ref(v___f_3298_);
v_fvarId_3309_ = lean_ctor_get(v_decl_3255_, 0);
v_y_3310_ = lean_ctor_get(v_decl_3255_, 2);
lean_inc_n(v___x_3270_, 2);
lean_inc(v_fvarId_3309_);
v___x_3311_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3309_, v___x_3270_, v_a_3256_);
lean_dec_ref(v___x_3311_);
lean_inc(v_y_3310_);
v___x_3312_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3310_, v___x_3270_, v_a_3256_);
v___y_3272_ = v___x_3312_;
goto v___jp_3271_;
}
case 5:
{
lean_object* v_fvarId_3313_; lean_object* v_y_3314_; lean_object* v_ty_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_fvarId_3313_ = lean_ctor_get(v_decl_3255_, 0);
v_y_3314_ = lean_ctor_get(v_decl_3255_, 3);
v_ty_3315_ = lean_ctor_get(v_decl_3255_, 4);
lean_inc_n(v___x_3270_, 2);
lean_inc(v_fvarId_3313_);
v___x_3316_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3313_, v___x_3270_, v_a_3256_);
lean_dec_ref(v___x_3316_);
lean_inc(v_y_3314_);
v___x_3317_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3314_, v___x_3270_, v_a_3256_);
lean_dec_ref(v___x_3317_);
lean_inc_ref(v_ty_3315_);
v___x_3318_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3298_, v_ty_3315_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
v___y_3272_ = v___x_3318_;
goto v___jp_3271_;
}
default: 
{
lean_object* v_fvarId_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v___f_3298_);
v_fvarId_3319_ = lean_ctor_get(v_decl_3255_, 0);
lean_inc(v___x_3270_);
lean_inc(v_fvarId_3319_);
v___x_3320_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3319_, v___x_3270_, v_a_3256_);
v___y_3272_ = v___x_3320_;
goto v___jp_3271_;
}
}
v___jp_3271_:
{
if (lean_obj_tag(v___y_3272_) == 0)
{
lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3296_; 
v_isSharedCheck_3296_ = !lean_is_exclusive(v___y_3272_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; 
v_unused_3297_ = lean_ctor_get(v___y_3272_, 0);
lean_dec(v_unused_3297_);
v___x_3274_ = v___y_3272_;
v_isShared_3275_ = v_isSharedCheck_3296_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v___y_3272_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3296_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v_decision_3277_; lean_object* v_newArms_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3295_; 
v___x_3276_ = lean_st_ref_take(v_a_3256_);
v_decision_3277_ = lean_ctor_get(v___x_3276_, 0);
v_newArms_3278_ = lean_ctor_get(v___x_3276_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3280_ = v___x_3276_;
v_isShared_3281_ = v_isSharedCheck_3295_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_newArms_3278_);
lean_inc(v_decision_3277_);
lean_dec(v___x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3295_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3282_ = lean_box(0);
v___x_3283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3278_, v___x_3270_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set_tag(v___x_3266_, 1);
lean_ctor_set(v___x_3266_, 1, v___x_3283_);
lean_ctor_set(v___x_3266_, 0, v_decl_3255_);
v___x_3285_ = v___x_3266_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_decl_3255_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3278_, v___x_3270_, v___x_3285_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3286_);
v___x_3288_ = v___x_3280_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_decision_3277_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_st_ref_put(v_a_3256_, v___x_3288_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3282_);
v___x_3291_ = v___x_3274_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3282_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3270_);
lean_del_object(v___x_3266_);
lean_dec_ref(v_decl_3255_);
return v___y_3272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec(v_a_3324_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
if (lean_obj_tag(v_as_x27_3332_) == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_b_3333_);
return v___x_3341_;
}
else
{
lean_object* v_head_3342_; lean_object* v_tail_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v_decision_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v_head_3342_ = lean_ctor_get(v_as_x27_3332_, 0);
v_tail_3343_ = lean_ctor_get(v_as_x27_3332_, 1);
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_st_ref_get(v___y_3334_);
v_decision_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc_ref(v_decision_3346_);
lean_dec(v___x_3345_);
v___x_3347_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3342_);
v___x_3348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3346_, v___x_3347_);
lean_dec(v___x_3347_);
lean_dec_ref(v_decision_3346_);
v___x_3349_ = lean_box(3);
v___x_3350_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3348_, v___x_3349_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = lean_box(2);
v___x_3352_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3348_, v___x_3351_);
lean_dec(v___x_3348_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; 
lean_inc(v_head_3342_);
v___x_3353_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3342_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_dec_ref_known(v___x_3353_, 1);
v_as_x27_3332_ = v_tail_3343_;
v_b_3333_ = v___x_3344_;
goto _start;
}
else
{
return v___x_3353_;
}
}
else
{
lean_object* v___x_3355_; 
lean_inc(v_head_3342_);
v___x_3355_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3342_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_dec_ref_known(v___x_3355_, 1);
v_as_x27_3332_ = v_tail_3343_;
v_b_3333_ = v___x_3344_;
goto _start;
}
else
{
return v___x_3355_;
}
}
}
else
{
uint8_t v___x_3357_; lean_object* v___x_3358_; 
lean_dec(v___x_3348_);
v___x_3357_ = 0;
v___x_3358_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3357_, v_head_3342_, v___y_3337_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_dec_ref_known(v___x_3358_, 1);
v_as_x27_3332_ = v_tail_3343_;
v_b_3333_ = v___x_3344_;
goto _start;
}
else
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3360_, v_b_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec(v_as_x27_3360_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_box(0);
v___x_3378_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3371_, v___x_3377_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v___x_3378_, 0);
lean_dec(v_unused_3386_);
v___x_3380_ = v___x_3378_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_dec(v___x_3378_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3377_);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3377_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
else
{
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec(v_a_3387_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3395_, lean_object* v_as_x27_3396_, lean_object* v_b_3397_, lean_object* v_a_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3396_, v_b_3397_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* v_as_3407_, lean_object* v_as_x27_3408_, lean_object* v_b_3409_, lean_object* v_a_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3407_, v_as_x27_3408_, v_b_3409_, v_a_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec(v_as_x27_3408_);
lean_dec(v_as_3407_);
return v_res_3418_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3422_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3423_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
lean_ctor_set(v___x_3425_, 2, v___x_3424_);
lean_ctor_set(v___x_3425_, 3, v___x_3424_);
lean_ctor_set(v___x_3425_, 4, v___x_3423_);
lean_ctor_set(v___x_3425_, 5, v___x_3423_);
lean_ctor_set(v___x_3425_, 6, v___x_3423_);
lean_ctor_set(v___x_3425_, 7, v___x_3423_);
lean_ctor_set(v___x_3425_, 8, v___x_3423_);
lean_ctor_set(v___x_3425_, 9, v___x_3423_);
lean_ctor_set(v___x_3425_, 10, v___x_3423_);
lean_ctor_set(v___x_3425_, 11, v___x_3422_);
return v___x_3425_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3426_; double v___x_3427_; 
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_float_of_nat(v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3431_, lean_object* v_msg_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_ref_3438_; lean_object* v___x_3439_; lean_object* v_env_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_ref_3438_ = lean_ctor_get(v___y_3435_, 2);
v___x_3439_ = lean_st_ref_get(v___y_3436_);
v_env_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc_ref(v_env_3440_);
lean_dec(v___x_3439_);
v___x_3441_ = lean_st_ref_get(v___y_3434_);
v___x_3442_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3433_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3502_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3502_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3502_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_lctx_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3500_; 
v_lctx_3447_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3441_, 1);
lean_dec(v_unused_3501_);
v___x_3449_ = v___x_3441_;
v_isShared_3450_ = v_isSharedCheck_3500_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_lctx_3447_);
lean_dec(v___x_3441_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3500_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3451_ = lean_unbox(v_a_3443_);
lean_dec(v_a_3443_);
v___x_3452_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3447_, v___x_3451_);
lean_dec_ref(v_lctx_3447_);
v___x_3453_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3435_);
v___x_3454_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3455_, 0, v_env_3440_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
lean_ctor_set(v___x_3455_, 2, v___x_3452_);
lean_ctor_set(v___x_3455_, 3, v___x_3453_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set_tag(v___x_3449_, 3);
lean_ctor_set(v___x_3449_, 1, v_msg_3432_);
lean_ctor_set(v___x_3449_, 0, v___x_3455_);
v___x_3457_ = v___x_3449_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_msg_3432_);
v___x_3457_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v_traceState_3459_; lean_object* v_env_3460_; lean_object* v_nextMacroScope_3461_; lean_object* v_ngen_3462_; lean_object* v_auxDeclNGen_3463_; lean_object* v_cache_3464_; lean_object* v_recordedDeps_3465_; lean_object* v_messages_3466_; lean_object* v_infoState_3467_; lean_object* v_snapshotTasks_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3498_; 
v___x_3458_ = lean_st_ref_take(v___y_3436_);
v_traceState_3459_ = lean_ctor_get(v___x_3458_, 4);
v_env_3460_ = lean_ctor_get(v___x_3458_, 0);
v_nextMacroScope_3461_ = lean_ctor_get(v___x_3458_, 1);
v_ngen_3462_ = lean_ctor_get(v___x_3458_, 2);
v_auxDeclNGen_3463_ = lean_ctor_get(v___x_3458_, 3);
v_cache_3464_ = lean_ctor_get(v___x_3458_, 5);
v_recordedDeps_3465_ = lean_ctor_get(v___x_3458_, 6);
v_messages_3466_ = lean_ctor_get(v___x_3458_, 7);
v_infoState_3467_ = lean_ctor_get(v___x_3458_, 8);
v_snapshotTasks_3468_ = lean_ctor_get(v___x_3458_, 9);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3470_ = v___x_3458_;
v_isShared_3471_ = v_isSharedCheck_3498_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snapshotTasks_3468_);
lean_inc(v_infoState_3467_);
lean_inc(v_messages_3466_);
lean_inc(v_recordedDeps_3465_);
lean_inc(v_cache_3464_);
lean_inc(v_traceState_3459_);
lean_inc(v_auxDeclNGen_3463_);
lean_inc(v_ngen_3462_);
lean_inc(v_nextMacroScope_3461_);
lean_inc(v_env_3460_);
lean_dec(v___x_3458_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3498_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
uint64_t v_tid_3472_; lean_object* v_traces_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3497_; 
v_tid_3472_ = lean_ctor_get_uint64(v_traceState_3459_, sizeof(void*)*1);
v_traces_3473_ = lean_ctor_get(v_traceState_3459_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_traceState_3459_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3475_ = v_traceState_3459_;
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_traces_3473_);
lean_dec(v_traceState_3459_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; double v___x_3479_; uint8_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_box(0);
v___x_3479_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3480_ = 0;
v___x_3481_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3482_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3482_, 0, v_cls_3431_);
lean_ctor_set(v___x_3482_, 1, v___x_3478_);
lean_ctor_set(v___x_3482_, 2, v___x_3481_);
lean_ctor_set_float(v___x_3482_, sizeof(void*)*3, v___x_3479_);
lean_ctor_set_float(v___x_3482_, sizeof(void*)*3 + 8, v___x_3479_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*3 + 16, v___x_3480_);
v___x_3483_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3484_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3457_);
lean_ctor_set(v___x_3484_, 2, v___x_3483_);
lean_inc(v_ref_3438_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_ref_3438_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = l_Lean_PersistentArray_push___redArg(v_traces_3473_, v___x_3485_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3486_);
v___x_3488_ = v___x_3475_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3486_);
lean_ctor_set_uint64(v_reuseFailAlloc_3496_, sizeof(void*)*1, v_tid_3472_);
v___x_3488_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 4, v___x_3488_);
v___x_3490_ = v___x_3470_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_env_3460_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_nextMacroScope_3461_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_ngen_3462_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_auxDeclNGen_3463_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 5, v_cache_3464_);
lean_ctor_set(v_reuseFailAlloc_3495_, 6, v_recordedDeps_3465_);
lean_ctor_set(v_reuseFailAlloc_3495_, 7, v_messages_3466_);
lean_ctor_set(v_reuseFailAlloc_3495_, 8, v_infoState_3467_);
lean_ctor_set(v_reuseFailAlloc_3495_, 9, v_snapshotTasks_3468_);
v___x_3490_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3491_ = lean_st_ref_put(v___y_3436_, v___x_3490_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3477_);
v___x_3493_ = v___x_3445_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3477_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
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
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v___x_3441_);
lean_dec_ref(v_env_3440_);
lean_dec_ref(v_msg_3432_);
lean_dec(v_cls_3431_);
v_a_3503_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3442_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3442_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3511_, lean_object* v_msg_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3511_, v_msg_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3519_, lean_object* v_msg_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3519_, v_msg_3520_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3528_, lean_object* v_msg_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3528_, v_msg_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
return v_res_3536_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3546_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3547_ = l_Lean_Name_append(v___x_3546_, v___x_3545_);
return v___x_3547_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
switch(lean_obj_tag(v_code_3554_))
{
case 0:
{
lean_object* v_decl_3561_; lean_object* v_k_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v_decl_3561_ = lean_ctor_get(v_code_3554_, 0);
lean_inc_ref(v_decl_3561_);
v_k_3562_ = lean_ctor_get(v_code_3554_, 1);
lean_inc_ref(v_k_3562_);
lean_dec_ref_known(v_code_3554_, 2);
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_decl_3561_);
v___x_3564_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3564_, 0, v_k_3562_);
v___x_3565_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3563_, v___x_3564_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
return v___x_3565_;
}
case 1:
{
lean_object* v_decl_3566_; lean_object* v_k_3567_; lean_object* v_params_3568_; lean_object* v_type_3569_; lean_object* v_value_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_decl_3566_ = lean_ctor_get(v_code_3554_, 0);
lean_inc_ref(v_decl_3566_);
v_k_3567_ = lean_ctor_get(v_code_3554_, 1);
lean_inc_ref(v_k_3567_);
lean_dec_ref_known(v_code_3554_, 2);
v_params_3568_ = lean_ctor_get(v_decl_3566_, 2);
lean_inc_ref(v_params_3568_);
v_type_3569_ = lean_ctor_get(v_decl_3566_, 3);
lean_inc_ref(v_type_3569_);
v_value_3570_ = lean_ctor_get(v_decl_3566_, 4);
v___x_3571_ = 0;
lean_inc_ref(v_value_3570_);
v___x_3572_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3572_, 0, v_value_3570_);
v___x_3573_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3572_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3593_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3593_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3593_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; 
v___x_3578_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3571_, v_decl_3566_, v_type_3569_, v_params_3568_, v_a_3574_, v_a_3557_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3578_, 1);
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 1);
lean_ctor_set(v___x_3576_, 0, v_a_3579_);
v___x_3581_ = v___x_3576_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3579_);
v___x_3581_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3582_, 0, v_k_3567_);
v___x_3583_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3581_, v___x_3582_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
return v___x_3583_;
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_del_object(v___x_3576_);
lean_dec_ref(v_k_3567_);
v_a_3585_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3578_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3578_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3569_);
lean_dec_ref(v_params_3568_);
lean_dec_ref(v_k_3567_);
lean_dec_ref(v_decl_3566_);
return v___x_3573_;
}
}
case 2:
{
lean_object* v_decl_3594_; lean_object* v_k_3595_; lean_object* v_params_3596_; lean_object* v_type_3597_; lean_object* v_value_3598_; uint8_t v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_decl_3594_ = lean_ctor_get(v_code_3554_, 0);
lean_inc_ref(v_decl_3594_);
v_k_3595_ = lean_ctor_get(v_code_3554_, 1);
lean_inc_ref(v_k_3595_);
lean_dec_ref_known(v_code_3554_, 2);
v_params_3596_ = lean_ctor_get(v_decl_3594_, 2);
lean_inc_ref(v_params_3596_);
v_type_3597_ = lean_ctor_get(v_decl_3594_, 3);
lean_inc_ref(v_type_3597_);
v_value_3598_ = lean_ctor_get(v_decl_3594_, 4);
v___x_3599_ = 0;
lean_inc_ref(v_value_3598_);
v___x_3600_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3600_, 0, v_value_3598_);
v___x_3601_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3600_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3621_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3621_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3621_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; 
v___x_3606_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3599_, v_decl_3594_, v_type_3597_, v_params_3596_, v_a_3602_, v_a_3557_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 2);
lean_ctor_set(v___x_3604_, 0, v_a_3607_);
v___x_3609_ = v___x_3604_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3607_);
v___x_3609_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3610_, 0, v_k_3595_);
v___x_3611_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3609_, v___x_3610_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
return v___x_3611_;
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_del_object(v___x_3604_);
lean_dec_ref(v_k_3595_);
v_a_3613_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3606_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3606_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3597_);
lean_dec_ref(v_params_3596_);
lean_dec_ref(v_k_3595_);
lean_dec_ref(v_decl_3594_);
return v___x_3601_;
}
}
case 4:
{
lean_object* v_cases_3622_; lean_object* v___x_3623_; 
v_cases_3622_ = lean_ctor_get(v_code_3554_, 0);
lean_inc_ref_n(v_cases_3622_, 2);
v___x_3623_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3622_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3622_);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_a_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_st_mk_ref(v___x_3626_);
v___x_3628_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3627_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; lean_object* v_typeName_3630_; lean_object* v_resultType_3631_; lean_object* v_discr_3632_; lean_object* v_alts_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3673_; 
lean_dec_ref_known(v___x_3628_, 1);
v___x_3629_ = lean_st_ref_get(v___x_3627_);
lean_dec(v___x_3627_);
v_typeName_3630_ = lean_ctor_get(v_cases_3622_, 0);
v_resultType_3631_ = lean_ctor_get(v_cases_3622_, 1);
v_discr_3632_ = lean_ctor_get(v_cases_3622_, 2);
v_alts_3633_ = lean_ctor_get(v_cases_3622_, 3);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_cases_3622_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3635_ = v_cases_3622_;
v_isShared_3636_ = v_isSharedCheck_3673_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_alts_3633_);
lean_inc(v_discr_3632_);
lean_inc(v_resultType_3631_);
lean_inc(v_typeName_3630_);
lean_dec(v_cases_3622_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3673_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_newArms_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v_newArms_3637_ = lean_ctor_get(v___x_3629_, 1);
lean_inc_ref(v_newArms_3637_);
lean_dec(v___x_3629_);
v___x_3638_ = lean_box(2);
v___x_3639_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3637_, v___x_3638_);
v___x_3640_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3633_);
v___x_3641_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3637_, v___x_3640_, v_alts_3633_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec_ref(v_newArms_3637_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3664_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3664_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3664_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___y_3647_; size_t v___x_3658_; size_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3658_ = lean_ptr_addr(v_alts_3633_);
lean_dec_ref(v_alts_3633_);
v___x_3659_ = lean_ptr_addr(v_a_3642_);
v___x_3660_ = lean_usize_dec_eq(v___x_3658_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_dec_ref_known(v_code_3554_, 1);
goto v___jp_3653_;
}
else
{
size_t v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = lean_ptr_addr(v_resultType_3631_);
v___x_3662_ = lean_usize_dec_eq(v___x_3661_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_dec_ref_known(v_code_3554_, 1);
goto v___jp_3653_;
}
else
{
uint8_t v___x_3663_; 
v___x_3663_ = l_Lean_instBEqFVarId_beq(v_discr_3632_, v_discr_3632_);
if (v___x_3663_ == 0)
{
lean_dec_ref_known(v_code_3554_, 1);
goto v___jp_3653_;
}
else
{
lean_dec(v_a_3642_);
lean_del_object(v___x_3635_);
lean_dec(v_discr_3632_);
lean_dec_ref(v_resultType_3631_);
lean_dec(v_typeName_3630_);
v___y_3647_ = v_code_3554_;
goto v___jp_3646_;
}
}
}
v___jp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3648_ = lean_array_mk(v___x_3639_);
v___x_3649_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_3648_, v___y_3647_);
lean_dec_ref(v___x_3648_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3649_);
v___x_3651_ = v___x_3644_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
v___jp_3653_:
{
lean_object* v___x_3655_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 3, v_a_3642_);
v___x_3655_ = v___x_3635_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_typeName_3630_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_resultType_3631_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_discr_3632_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_a_3642_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
v___y_3647_ = v___x_3656_;
goto v___jp_3646_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec(v___x_3639_);
lean_del_object(v___x_3635_);
lean_dec_ref(v_alts_3633_);
lean_dec(v_discr_3632_);
lean_dec_ref(v_resultType_3631_);
lean_dec(v_typeName_3630_);
lean_dec_ref_known(v_code_3554_, 1);
v_a_3665_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3641_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3641_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v___x_3627_);
lean_dec_ref_known(v_code_3554_, 1);
lean_dec_ref(v_cases_3622_);
v_a_3674_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3628_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3628_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref_known(v_code_3554_, 1);
lean_dec_ref(v_cases_3622_);
v_a_3682_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3623_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3623_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
default: 
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_inc(v_a_3555_);
v___x_3690_ = lean_array_mk(v_a_3555_);
v___x_3691_ = l_Array_reverse___redArg(v___x_3690_);
v___x_3692_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_3691_, v_code_3554_);
lean_dec_ref(v___x_3691_);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
lean_dec(v_a_3695_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3702_, lean_object* v_i_3703_, lean_object* v_as_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = lean_array_get_size(v_as_3704_);
v___x_3712_ = lean_nat_dec_lt(v_i_3703_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_dec(v_i_3703_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v_as_3704_);
return v___x_3713_;
}
else
{
lean_object* v_toCold_3714_; lean_object* v_options_3715_; lean_object* v_inheritedTraceOptions_3716_; uint8_t v_hasTrace_3717_; lean_object* v_a_3718_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; 
v_toCold_3714_ = lean_ctor_get(v___y_3708_, 0);
v_options_3715_ = lean_ctor_get(v_toCold_3714_, 2);
v_inheritedTraceOptions_3716_ = lean_ctor_get(v_toCold_3714_, 11);
v_hasTrace_3717_ = lean_ctor_get_uint8(v_options_3715_, sizeof(void*)*1);
v_a_3718_ = lean_array_fget_borrowed(v_as_3704_, v_i_3703_);
v___x_3749_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3718_);
v___x_3750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3702_, v___x_3749_);
if (v_hasTrace_3717_ == 0)
{
lean_dec(v___x_3749_);
v___y_3752_ = v___y_3706_;
v___y_3753_ = v___y_3707_;
v___y_3754_ = v___y_3708_;
v___y_3755_ = v___y_3709_;
goto v___jp_3751_;
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3760_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3761_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3716_, v_options_3715_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_dec(v___x_3749_);
v___y_3752_ = v___y_3706_;
v___y_3753_ = v___y_3707_;
v___y_3754_ = v___y_3708_;
v___y_3755_ = v___y_3709_;
goto v___jp_3751_;
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3763_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3764_ = lean_unsigned_to_nat(0u);
v___x_3765_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3749_, v___x_3764_);
v___x_3766_ = l_Lean_MessageData_ofFormat(v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3763_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = l_List_lengthTR___redArg(v___x_3750_);
v___x_3771_ = l_Nat_reprFast(v___x_3770_);
v___x_3772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
v___x_3773_ = l_Lean_MessageData_ofFormat(v___x_3772_);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3769_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3760_, v___x_3774_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_dec_ref_known(v___x_3775_, 1);
v___y_3752_ = v___y_3706_;
v___y_3753_ = v___y_3707_;
v___y_3754_ = v___y_3708_;
v___y_3755_ = v___y_3709_;
goto v___jp_3751_;
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v___x_3750_);
lean_dec_ref(v_as_3704_);
lean_dec(v_i_3703_);
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
v___jp_3719_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_3721_, v___y_3725_);
lean_dec_ref(v___y_3721_);
v___x_3727_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3727_, 0, v___x_3726_);
v___x_3728_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3727_, v___y_3720_, v___y_3723_, v___y_3724_, v___y_3722_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v___x_3730_; size_t v___x_3731_; size_t v___x_3732_; uint8_t v___x_3733_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3728_, 1);
lean_inc(v_a_3718_);
v___x_3730_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3718_, v_a_3729_);
v___x_3731_ = lean_ptr_addr(v_a_3718_);
v___x_3732_ = lean_ptr_addr(v___x_3730_);
v___x_3733_ = lean_usize_dec_eq(v___x_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = lean_unsigned_to_nat(1u);
v___x_3735_ = lean_nat_add(v_i_3703_, v___x_3734_);
v___x_3736_ = lean_array_fset(v_as_3704_, v_i_3703_, v___x_3730_);
lean_dec(v_i_3703_);
v_i_3703_ = v___x_3735_;
v_as_3704_ = v___x_3736_;
goto _start;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref(v___x_3730_);
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = lean_nat_add(v_i_3703_, v___x_3738_);
lean_dec(v_i_3703_);
v_i_3703_ = v___x_3739_;
goto _start;
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_as_3704_);
lean_dec(v_i_3703_);
v_a_3741_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3728_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3728_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
v___jp_3751_:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_array_mk(v___x_3750_);
switch(lean_obj_tag(v_a_3718_))
{
case 0:
{
lean_object* v_code_3757_; 
v_code_3757_ = lean_ctor_get(v_a_3718_, 2);
lean_inc_ref(v_code_3757_);
v___y_3720_ = v___y_3752_;
v___y_3721_ = v___x_3756_;
v___y_3722_ = v___y_3755_;
v___y_3723_ = v___y_3753_;
v___y_3724_ = v___y_3754_;
v___y_3725_ = v_code_3757_;
goto v___jp_3719_;
}
case 1:
{
lean_object* v_code_3758_; 
v_code_3758_ = lean_ctor_get(v_a_3718_, 1);
lean_inc_ref(v_code_3758_);
v___y_3720_ = v___y_3752_;
v___y_3721_ = v___x_3756_;
v___y_3722_ = v___y_3755_;
v___y_3723_ = v___y_3753_;
v___y_3724_ = v___y_3754_;
v___y_3725_ = v_code_3758_;
goto v___jp_3719_;
}
default: 
{
lean_object* v_code_3759_; 
v_code_3759_ = lean_ctor_get(v_a_3718_, 0);
lean_inc_ref(v_code_3759_);
v___y_3720_ = v___y_3752_;
v___y_3721_ = v___x_3756_;
v___y_3722_ = v___y_3755_;
v___y_3723_ = v___y_3753_;
v___y_3724_ = v___y_3754_;
v___y_3725_ = v_code_3759_;
goto v___jp_3719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3784_, lean_object* v_i_3785_, lean_object* v_as_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3784_, v_i_3785_, v_as_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___x_3784_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3794_, lean_object* v_v_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
if (lean_obj_tag(v_v_3795_) == 0)
{
lean_object* v_code_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3826_; 
v_code_3802_ = lean_ctor_get(v_v_3795_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_v_3795_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3804_ = v_v_3795_;
v_isShared_3805_ = v_isSharedCheck_3826_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_code_3802_);
lean_dec(v_v_3795_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3826_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; 
lean_inc(v___y_3800_);
lean_inc_ref(v___y_3799_);
lean_inc(v___y_3798_);
lean_inc_ref(v___y_3797_);
lean_inc(v___y_3796_);
v___x_3806_ = lean_apply_7(v_f_3794_, v_code_3802_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, lean_box(0));
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3817_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v_a_3807_);
v___x_3812_ = v___x_3804_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3814_ = v___x_3809_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3804_);
v_a_3818_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3806_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3806_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
else
{
lean_object* v___x_3827_; 
lean_dec_ref(v_f_3794_);
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_v_3795_);
return v___x_3827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3828_, lean_object* v_v_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3828_, v_v_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3837_, lean_object* v_f_3838_, lean_object* v_v_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3838_, v_v_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3847_, lean_object* v_f_3848_, lean_object* v_v_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
uint8_t v_pu_boxed_3856_; lean_object* v_res_3857_; 
v_pu_boxed_3856_ = lean_unbox(v_pu_3847_);
v_res_3857_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_3856_, v_f_3848_, v_v_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_toSignature_3865_; lean_object* v_value_3866_; uint8_t v_recursive_3867_; lean_object* v_inlineAttr_x3f_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3894_; 
v_toSignature_3865_ = lean_ctor_get(v_decl_3859_, 0);
v_value_3866_ = lean_ctor_get(v_decl_3859_, 1);
v_recursive_3867_ = lean_ctor_get_uint8(v_decl_3859_, sizeof(void*)*3);
v_inlineAttr_x3f_3868_ = lean_ctor_get(v_decl_3859_, 2);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_decl_3859_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3870_ = v_decl_3859_;
v_isShared_3871_ = v_isSharedCheck_3894_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_inlineAttr_x3f_3868_);
lean_inc(v_value_3866_);
lean_inc(v_toSignature_3865_);
lean_dec(v_decl_3859_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3894_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_3873_ = lean_box(0);
v___x_3874_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_3872_, v_value_3866_, v___x_3873_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3885_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3885_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3885_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v_a_3875_);
v___x_3880_ = v___x_3870_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_toSignature_3865_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_a_3875_);
lean_ctor_set(v_reuseFailAlloc_3884_, 2, v_inlineAttr_x3f_3868_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, sizeof(void*)*3, v_recursive_3867_);
v___x_3880_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3882_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3880_);
v___x_3882_ = v___x_3877_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_del_object(v___x_3870_);
lean_dec(v_inlineAttr_x3f_3868_);
lean_dec_ref(v_toSignature_3865_);
v_a_3886_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3874_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3874_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(lean_object* v_decl_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_3918_, lean_object* v___f_3919_, lean_object* v_occurrence_3920_, lean_object* v_h_3921_){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_3923_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3922_, v_phase_3918_, v___f_3919_, v_occurrence_3920_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_3924_, lean_object* v___f_3925_, lean_object* v_occurrence_3926_, lean_object* v_h_3927_){
_start:
{
uint8_t v_phase_boxed_3928_; lean_object* v_res_3929_; 
v_phase_boxed_3928_ = lean_unbox(v_phase_3924_);
v_res_3929_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_3928_, v___f_3925_, v_occurrence_3926_, v_h_3927_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_3931_, lean_object* v_occurrence_3932_){
_start:
{
lean_object* v___f_3933_; lean_object* v___x_3934_; lean_object* v___f_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; lean_object* v___x_3938_; 
v___f_3933_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_3934_ = lean_box(v_phase_3931_);
v___f_3935_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3935_, 0, v___x_3934_);
lean_closure_set(v___f_3935_, 1, v___f_3933_);
lean_closure_set(v___f_3935_, 2, v_occurrence_3932_);
v___x_3936_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_3937_ = 0;
v___x_3938_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_3936_, v_phase_3931_, v___x_3937_, v___f_3935_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_3939_, lean_object* v_occurrence_3940_){
_start:
{
uint8_t v_phase_boxed_3941_; lean_object* v_res_3942_; 
v_phase_boxed_3941_ = lean_unbox(v_phase_3939_);
v_res_3942_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_3941_, v_occurrence_3940_);
return v_res_3942_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = lean_unsigned_to_nat(3411573818u);
v___x_3995_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_3996_ = l_Lean_Name_num___override(v___x_3995_, v___x_3994_);
return v___x_3996_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_3999_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4000_ = l_Lean_Name_str___override(v___x_3999_, v___x_3998_);
return v___x_4000_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4003_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4004_ = l_Lean_Name_str___override(v___x_4003_, v___x_4002_);
return v___x_4004_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_unsigned_to_nat(2u);
v___x_4006_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4007_ = l_Lean_Name_num___override(v___x_4006_, v___x_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4009_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4010_ = 1;
v___x_4011_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4012_ = l_Lean_registerTraceClass(v___x_4009_, v___x_4010_, v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4014_;
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
