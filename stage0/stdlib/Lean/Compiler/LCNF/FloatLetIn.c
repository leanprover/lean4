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
uint64_t l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(lean_object* v_x_53_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_53_ = stack[0].m_obj;
uint64_t v_res_62_;
v_res_62_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_x_53_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed(lean_object* v_x_63_){
_start:
{
uint64_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_x_63_);
lean_dec(v_x_63_);
v_r_65_ = lean_box_uint64(v_res_64_);
return v_r_65_;
}
}
uint8_t l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v_name_70_; lean_object* v_name_71_; uint8_t v___x_72_; 
v_name_70_ = lean_ctor_get(v_x_68_, 0);
v_name_71_ = lean_ctor_get(v_x_69_, 0);
v___x_72_ = lean_name_eq(v_name_70_, v_name_71_);
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
case 1:
{
if (lean_obj_tag(v_x_69_) == 1)
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
case 2:
{
if (lean_obj_tag(v_x_69_) == 2)
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
default: 
{
if (lean_obj_tag(v_x_69_) == 3)
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_68_ = stack[0].m_obj;
lean_object* v_x_69_ = stack[1].m_obj;
uint8_t v_res_80_;
v_res_80_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_x_68_, v_x_69_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = lean_nat_to_int(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_to_int(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
lean_object* v___y_113_; lean_object* v___y_120_; lean_object* v___y_127_; 
switch(lean_obj_tag(v_x_110_))
{
case 0:
{
lean_object* v_name_133_; lean_object* v___y_135_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_name_133_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_name_133_);
lean_dec_ref_known(v_x_110_, 1);
v___x_144_ = lean_unsigned_to_nat(1024u);
v___x_145_ = lean_nat_dec_le(v___x_144_, v_prec_111_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_135_ = v___x_146_;
goto v___jp_134_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_135_ = v___x_147_;
goto v___jp_134_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_136_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8));
v___x_137_ = lean_unsigned_to_nat(1024u);
v___x_138_ = l_Lean_Name_reprPrec(v_name_133_, v___x_137_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_136_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
lean_inc(v___y_135_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_135_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_111_);
return v___x_143_;
}
}
case 1:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1024u);
v___x_149_ = lean_nat_dec_le(v___x_148_, v_prec_111_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_113_ = v___x_150_;
goto v___jp_112_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_113_ = v___x_151_;
goto v___jp_112_;
}
}
case 2:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_prec_111_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_120_ = v___x_154_;
goto v___jp_119_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_120_ = v___x_155_;
goto v___jp_119_;
}
}
default: 
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1024u);
v___x_157_ = lean_nat_dec_le(v___x_156_, v_prec_111_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
v___y_127_ = v___x_158_;
goto v___jp_126_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10, &l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
v___y_127_ = v___x_159_;
goto v___jp_126_;
}
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_114_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1));
lean_inc(v___y_113_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v_prec_111_);
return v___x_118_;
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3));
lean_inc(v___y_120_);
v___x_122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_122_, 0, v___y_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = 0;
v___x_124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set_uint8(v___x_124_, sizeof(void*)*1, v___x_123_);
v___x_125_ = l_Repr_addAppParen(v___x_124_, v_prec_111_);
return v___x_125_;
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_128_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5));
lean_inc(v___y_127_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___y_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_130_);
v___x_132_ = l_Repr_addAppParen(v___x_131_, v_prec_111_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed(lean_object* v_x_160_, lean_object* v_prec_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v_x_160_, v_prec_161_);
lean_dec(v_prec_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v_ctorName_166_; lean_object* v___x_167_; 
v_ctorName_166_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_ctorName_166_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v_ctorName_166_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(1);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object* v_x_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_x_169_);
lean_dec_ref(v_x_169_);
return v_res_170_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object* v_decl_171_, lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_inc(v_a_173_);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v_decl_171_);
lean_ctor_set(v___x_179_, 1, v_a_173_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
v___x_180_ = lean_apply_6(v_x_172_, v___x_179_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, lean_box(0));
return v___x_180_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_171_ = stack[0].m_obj;
lean_object* v_x_172_ = stack[1].m_obj;
lean_object* v_a_173_ = stack[2].m_obj;
lean_object* v_a_174_ = stack[3].m_obj;
lean_object* v_a_175_ = stack[4].m_obj;
lean_object* v_a_176_ = stack[5].m_obj;
lean_object* v_a_177_ = stack[6].m_obj;
lean_object* v_res_181_;
v_res_181_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_171_, v_x_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg___boxed(lean_object* v_decl_182_, lean_object* v_x_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_182_, v_x_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
return v_res_190_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* v_00_u03b1_191_, lean_object* v_decl_192_, lean_object* v_x_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v_decl_192_, v_x_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
return v___x_200_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_192_ = stack[1].m_obj;
lean_object* v_x_193_ = stack[2].m_obj;
lean_object* v_a_194_ = stack[3].m_obj;
lean_object* v_a_195_ = stack[4].m_obj;
lean_object* v_a_196_ = stack[5].m_obj;
lean_object* v_a_197_ = stack[6].m_obj;
lean_object* v_a_198_ = stack[7].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_box(0), v_decl_192_, v_x_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___boxed(lean_object* v_00_u03b1_202_, lean_object* v_decl_203_, lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(v_00_u03b1_202_, v_decl_203_, v_x_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
return v_res_211_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_box(0);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
v___x_219_ = lean_apply_6(v_x_212_, v___x_218_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_212_ = stack[0].m_obj;
lean_object* v_a_213_ = stack[1].m_obj;
lean_object* v_a_214_ = stack[2].m_obj;
lean_object* v_a_215_ = stack[3].m_obj;
lean_object* v_a_216_ = stack[4].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg___boxed(lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* v_00_u03b1_228_, lean_object* v_x_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v_x_229_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_withNewScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_229_ = stack[1].m_obj;
lean_object* v_a_230_ = stack[2].m_obj;
lean_object* v_a_231_ = stack[3].m_obj;
lean_object* v_a_232_ = stack[4].m_obj;
lean_object* v_a_233_ = stack[5].m_obj;
lean_object* v_a_234_ = stack[6].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_box(0), v_x_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
stack->m_obj
 = v_res_237_;
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
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object* v_decl_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_247_ = stack[0].m_obj;
lean_object* v_a_248_ = stack[1].m_obj;
lean_object* v_a_249_ = stack[2].m_obj;
lean_object* v_a_250_ = stack[3].m_obj;
lean_object* v_a_251_ = stack[4].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object* v_decl_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_320_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* v_decl_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_321_ = stack[0].m_obj;
lean_object* v_a_322_ = stack[1].m_obj;
lean_object* v_a_323_ = stack[2].m_obj;
lean_object* v_a_324_ = stack[3].m_obj;
lean_object* v_a_325_ = stack[4].m_obj;
lean_object* v_a_326_ = stack[5].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(v_decl_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
stack->m_obj
 = v_res_329_;
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(lean_object* v_a_338_, lean_object* v_x_339_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_338_ = stack[0].m_obj;
lean_object* v_x_339_ = stack[1].m_obj;
uint8_t v_res_345_;
v_res_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_338_, v_x_339_);
stack->m_num = v_res_345_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(lean_object* v_a_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_346_, v_x_347_);
lean_dec(v_x_347_);
lean_dec(v_a_346_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_buckets_352_; lean_object* v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v_fold_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_buckets_352_ = lean_ctor_get(v_m_350_, 1);
v___x_353_ = lean_array_get_size(v_buckets_352_);
v___x_354_ = l_Lean_instHashableFVarId_hash(v_a_351_);
v___x_355_ = 32ULL;
v___x_356_ = lean_uint64_shift_right(v___x_354_, v___x_355_);
v_fold_357_ = lean_uint64_xor(v___x_354_, v___x_356_);
v___x_358_ = 16ULL;
v___x_359_ = lean_uint64_shift_right(v_fold_357_, v___x_358_);
v___x_360_ = lean_uint64_xor(v_fold_357_, v___x_359_);
v___x_361_ = lean_uint64_to_usize(v___x_360_);
v___x_362_ = lean_usize_of_nat(v___x_353_);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_sub(v___x_362_, v___x_363_);
v___x_365_ = lean_usize_land(v___x_361_, v___x_364_);
v___x_366_ = lean_array_uget_borrowed(v_buckets_352_, v___x_365_);
v___x_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_351_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_350_ = stack[0].m_obj;
lean_object* v_a_351_ = stack[1].m_obj;
uint8_t v_res_368_;
v_res_368_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_350_, v_a_351_);
stack->m_num = v_res_368_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(lean_object* v_m_369_, lean_object* v_a_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_m_369_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
return v_x_373_;
}
else
{
lean_object* v_key_375_; lean_object* v_value_376_; lean_object* v_tail_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_400_; 
v_key_375_ = lean_ctor_get(v_x_374_, 0);
v_value_376_ = lean_ctor_get(v_x_374_, 1);
v_tail_377_ = lean_ctor_get(v_x_374_, 2);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_400_ == 0)
{
v___x_379_ = v_x_374_;
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_tail_377_);
lean_inc(v_value_376_);
lean_inc(v_key_375_);
lean_dec(v_x_374_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v_fold_385_; uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v___x_388_; size_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_381_ = lean_array_get_size(v_x_373_);
v___x_382_ = l_Lean_instHashableFVarId_hash(v_key_375_);
v___x_383_ = 32ULL;
v___x_384_ = lean_uint64_shift_right(v___x_382_, v___x_383_);
v_fold_385_ = lean_uint64_xor(v___x_382_, v___x_384_);
v___x_386_ = 16ULL;
v___x_387_ = lean_uint64_shift_right(v_fold_385_, v___x_386_);
v___x_388_ = lean_uint64_xor(v_fold_385_, v___x_387_);
v___x_389_ = lean_uint64_to_usize(v___x_388_);
v___x_390_ = lean_usize_of_nat(v___x_381_);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_sub(v___x_390_, v___x_391_);
v___x_393_ = lean_usize_land(v___x_389_, v___x_392_);
v___x_394_ = lean_array_uget_borrowed(v_x_373_, v___x_393_);
lean_inc(v___x_394_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 2, v___x_394_);
v___x_396_ = v___x_379_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_key_375_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_value_376_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_394_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_array_uset(v_x_373_, v___x_393_, v___x_396_);
v_x_373_ = v___x_397_;
v_x_374_ = v_tail_377_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(lean_object* v_i_401_, lean_object* v_source_402_, lean_object* v_target_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_array_get_size(v_source_402_);
v___x_405_ = lean_nat_dec_lt(v_i_401_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec_ref(v_source_402_);
lean_dec(v_i_401_);
return v_target_403_;
}
else
{
lean_object* v_es_406_; lean_object* v___x_407_; lean_object* v_source_408_; lean_object* v_target_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_es_406_ = lean_array_fget(v_source_402_, v_i_401_);
v___x_407_ = lean_box(0);
v_source_408_ = lean_array_fset(v_source_402_, v_i_401_, v___x_407_);
v_target_409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_target_403_, v_es_406_);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_i_401_, v___x_410_);
lean_dec(v_i_401_);
v_i_401_ = v___x_411_;
v_source_402_ = v_source_408_;
v_target_403_ = v_target_409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(lean_object* v_data_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_nbuckets_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_414_ = lean_array_get_size(v_data_413_);
v___x_415_ = lean_unsigned_to_nat(2u);
v_nbuckets_416_ = lean_nat_mul(v___x_414_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_box(0);
v___x_419_ = lean_mk_array(v_nbuckets_416_, v___x_418_);
v___x_420_ = lean_array_propagate_mark(v_data_413_, v___x_419_);
v___x_421_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v___x_417_, v_data_413_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_b_424_){
_start:
{
lean_object* v_size_425_; lean_object* v_buckets_426_; lean_object* v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v_fold_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v_bkt_440_; uint8_t v___x_441_; 
v_size_425_ = lean_ctor_get(v_m_422_, 0);
v_buckets_426_ = lean_ctor_get(v_m_422_, 1);
v___x_427_ = lean_array_get_size(v_buckets_426_);
v___x_428_ = l_Lean_instHashableFVarId_hash(v_a_423_);
v___x_429_ = 32ULL;
v___x_430_ = lean_uint64_shift_right(v___x_428_, v___x_429_);
v_fold_431_ = lean_uint64_xor(v___x_428_, v___x_430_);
v___x_432_ = 16ULL;
v___x_433_ = lean_uint64_shift_right(v_fold_431_, v___x_432_);
v___x_434_ = lean_uint64_xor(v_fold_431_, v___x_433_);
v___x_435_ = lean_uint64_to_usize(v___x_434_);
v___x_436_ = lean_usize_of_nat(v___x_427_);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_sub(v___x_436_, v___x_437_);
v___x_439_ = lean_usize_land(v___x_435_, v___x_438_);
v_bkt_440_ = lean_array_uget_borrowed(v_buckets_426_, v___x_439_);
v___x_441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_423_, v_bkt_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_462_; 
lean_inc_ref(v_buckets_426_);
lean_inc(v_size_425_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_m_422_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; 
v_unused_463_ = lean_ctor_get(v_m_422_, 1);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_m_422_, 0);
lean_dec(v_unused_464_);
v___x_443_ = v_m_422_;
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
else
{
lean_dec(v_m_422_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v_size_x27_446_; lean_object* v___x_447_; lean_object* v_buckets_x27_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v_size_x27_446_ = lean_nat_add(v_size_425_, v___x_445_);
lean_dec(v_size_425_);
lean_inc(v_bkt_440_);
v___x_447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_447_, 0, v_a_423_);
lean_ctor_set(v___x_447_, 1, v_b_424_);
lean_ctor_set(v___x_447_, 2, v_bkt_440_);
v_buckets_x27_448_ = lean_array_uset(v_buckets_426_, v___x_439_, v___x_447_);
v___x_449_ = lean_unsigned_to_nat(4u);
v___x_450_ = lean_nat_mul(v_size_x27_446_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = lean_nat_div(v___x_450_, v___x_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_array_get_size(v_buckets_x27_448_);
v___x_454_ = lean_nat_dec_le(v___x_452_, v___x_453_);
lean_dec(v___x_452_);
if (v___x_454_ == 0)
{
lean_object* v_val_455_; lean_object* v___x_457_; 
v_val_455_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_448_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_val_455_);
lean_ctor_set(v___x_443_, 0, v_size_x27_446_);
v___x_457_ = v___x_443_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_size_x27_446_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_val_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_object* v___x_460_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_buckets_x27_448_);
lean_ctor_set(v___x_443_, 0, v_size_x27_446_);
v___x_460_ = v___x_443_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_size_x27_446_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_buckets_x27_448_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_dec(v_b_424_);
lean_dec(v_a_423_);
return v_m_422_;
}
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(lean_object* v_var_465_, uint8_t v_borrowed_466_, lean_object* v_a_467_){
_start:
{
if (lean_obj_tag(v_var_465_) == 1)
{
lean_object* v_fvarId_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_487_; 
v_fvarId_469_ = lean_ctor_get(v_var_465_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_var_465_);
if (v_isSharedCheck_487_ == 0)
{
v___x_471_ = v_var_465_;
v_isShared_472_ = v_isSharedCheck_487_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_fvarId_469_);
lean_dec(v_var_465_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_487_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_st_ref_get(v_a_467_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_473_, v_fvarId_469_);
lean_dec(v___x_473_);
if (v_borrowed_466_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_475_ = lean_st_ref_take(v_a_467_);
v___x_476_ = lean_box(0);
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_475_, v_fvarId_469_, v___x_476_);
v___x_478_ = lean_st_ref_put(v_a_467_, v___x_477_);
v___x_479_ = lean_box(v___x_474_);
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 0);
lean_ctor_set(v___x_471_, 0, v___x_479_);
v___x_481_ = v___x_471_;
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
else
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_fvarId_469_);
v___x_483_ = lean_box(v___x_474_);
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 0);
lean_ctor_set(v___x_471_, 0, v___x_483_);
v___x_485_ = v___x_471_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_var_465_);
v___x_488_ = 0;
v___x_489_ = lean_box(v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_var_465_ = stack[0].m_obj;
uint8_t v_borrowed_466_ = stack[1].m_num;
lean_object* v_a_467_ = stack[2].m_obj;
lean_object* v_res_491_;
v_res_491_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_465_, v_borrowed_466_, v_a_467_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(lean_object* v_var_492_, lean_object* v_borrowed_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
uint8_t v_borrowed_boxed_496_; lean_object* v_res_497_; 
v_borrowed_boxed_496_ = lean_unbox(v_borrowed_493_);
v_res_497_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_492_, v_borrowed_boxed_496_, v_a_494_);
lean_dec(v_a_494_);
return v_res_497_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(lean_object* v_var_498_, uint8_t v_borrowed_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_498_, v_borrowed_499_, v_a_500_);
return v___x_506_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_var_498_ = stack[0].m_obj;
uint8_t v_borrowed_499_ = stack[1].m_num;
lean_object* v_a_500_ = stack[2].m_obj;
lean_object* v_a_501_ = stack[3].m_obj;
lean_object* v_a_502_ = stack[4].m_obj;
lean_object* v_a_503_ = stack[5].m_obj;
lean_object* v_a_504_ = stack[6].m_obj;
lean_object* v_res_507_;
v_res_507_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_498_, v_borrowed_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(lean_object* v_var_508_, lean_object* v_borrowed_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
uint8_t v_borrowed_boxed_516_; lean_object* v_res_517_; 
v_borrowed_boxed_516_ = lean_unbox(v_borrowed_509_);
v_res_517_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_508_, v_borrowed_boxed_516_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
return v_res_517_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_a_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_519_, v_a_520_);
return v___x_521_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_519_ = stack[1].m_obj;
lean_object* v_a_520_ = stack[2].m_obj;
uint8_t v_res_522_;
v_res_522_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(lean_box(0), v_m_519_, v_a_520_);
stack->m_num = v_res_522_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(lean_object* v_00_u03b2_523_, lean_object* v_m_524_, lean_object* v_a_525_){
_start:
{
uint8_t v_res_526_; lean_object* v_r_527_; 
v_res_526_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_523_, v_m_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_m_524_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(lean_object* v_00_u03b2_528_, lean_object* v_m_529_, lean_object* v_a_530_, lean_object* v_b_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_529_, v_a_530_, v_b_531_);
return v___x_532_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_534_ = stack[1].m_obj;
lean_object* v_x_535_ = stack[2].m_obj;
uint8_t v_res_537_;
v_res_537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(lean_box(0), v_a_534_, v_x_535_);
stack->m_num = v_res_537_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(lean_object* v_00_u03b2_538_, lean_object* v_a_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_538_, v_a_539_, v_x_540_);
lean_dec(v_x_540_);
lean_dec(v_a_539_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(lean_object* v_00_u03b2_543_, lean_object* v_data_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_data_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_546_, lean_object* v_i_547_, lean_object* v_source_548_, lean_object* v_target_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v_i_547_, v_source_548_, v_target_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_x_552_, v_x_553_);
return v___x_554_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(lean_object* v_as_555_, size_t v_i_556_, size_t v_stop_557_, uint8_t v_b_558_, lean_object* v___y_559_){
_start:
{
uint8_t v_a_562_; lean_object* v___y_567_; uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_556_, v_stop_557_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_array_uget_borrowed(v_as_555_, v_i_556_);
lean_inc(v___x_571_);
v___x_572_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_571_, v___x_570_, v___y_559_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; uint8_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v___x_574_ = lean_unbox(v_a_573_);
if (v___x_574_ == 0)
{
lean_dec_ref_known(v___x_572_, 1);
v_a_562_ = v_b_558_;
goto v___jp_561_;
}
else
{
v___y_567_ = v___x_572_;
goto v___jp_566_;
}
}
else
{
v___y_567_ = v___x_572_;
goto v___jp_566_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_box(v_b_558_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
v___jp_561_:
{
size_t v___x_563_; size_t v___x_564_; 
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_556_, v___x_563_);
v_i_556_ = v___x_564_;
v_b_558_ = v_a_562_;
goto _start;
}
v___jp_566_:
{
if (lean_obj_tag(v___y_567_) == 0)
{
lean_object* v_a_568_; uint8_t v___x_569_; 
v_a_568_ = lean_ctor_get(v___y_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___y_567_, 1);
v___x_569_ = lean_unbox(v_a_568_);
lean_dec(v_a_568_);
v_a_562_ = v___x_569_;
goto v___jp_561_;
}
else
{
return v___y_567_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_555_ = stack[0].m_obj;
size_t v_i_556_ = stack[1].m_num;
size_t v_stop_557_ = stack[2].m_num;
uint8_t v_b_558_ = stack[3].m_num;
lean_object* v___y_559_ = stack[4].m_obj;
lean_object* v_res_577_;
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_555_, v_i_556_, v_stop_557_, v_b_558_, v___y_559_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(lean_object* v_as_578_, lean_object* v_i_579_, lean_object* v_stop_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_stop_boxed_585_; uint8_t v_b_boxed_586_; lean_object* v_res_587_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_579_);
lean_dec(v_i_579_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_580_);
lean_dec(v_stop_580_);
v_b_boxed_586_ = lean_unbox(v_b_581_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_578_, v_i_boxed_584_, v_stop_boxed_585_, v_b_boxed_586_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v_as_578_);
return v_res_587_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(lean_object* v_upperBound_588_, lean_object* v_args_589_, lean_object* v_val_590_, lean_object* v_a_591_, uint8_t v_b_592_, lean_object* v___y_593_){
_start:
{
uint8_t v_a_596_; uint8_t v___x_600_; 
v___x_600_ = lean_nat_dec_lt(v_a_591_, v_upperBound_588_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_a_591_);
v___x_601_ = lean_box(v_b_592_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v_params_603_; lean_object* v___x_604_; uint8_t v___y_606_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_params_603_ = lean_ctor_get(v_val_590_, 3);
v___x_604_ = lean_array_fget_borrowed(v_args_589_, v_a_591_);
v___x_610_ = lean_array_get_size(v_params_603_);
v___x_611_ = lean_nat_dec_lt(v_a_591_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_606_ = v___x_611_;
goto v___jp_605_;
}
else
{
lean_object* v___x_612_; uint8_t v_borrow_613_; 
v___x_612_ = lean_array_fget_borrowed(v_params_603_, v_a_591_);
v_borrow_613_ = lean_ctor_get_uint8(v___x_612_, sizeof(void*)*3);
v___y_606_ = v_borrow_613_;
goto v___jp_605_;
}
v___jp_605_:
{
lean_object* v___x_607_; 
lean_inc(v___x_604_);
v___x_607_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_604_, v___y_606_, v___y_593_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; uint8_t v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = lean_unbox(v_a_608_);
lean_dec(v_a_608_);
if (v___x_609_ == 0)
{
v_a_596_ = v_b_592_;
goto v___jp_595_;
}
else
{
v_a_596_ = v___x_600_;
goto v___jp_595_;
}
}
else
{
lean_dec(v_a_591_);
return v___x_607_;
}
}
}
v___jp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_a_591_, v___x_597_);
lean_dec(v_a_591_);
v_a_591_ = v___x_598_;
v_b_592_ = v_a_596_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_588_ = stack[0].m_obj;
lean_object* v_args_589_ = stack[1].m_obj;
lean_object* v_val_590_ = stack[2].m_obj;
lean_object* v_a_591_ = stack[3].m_obj;
uint8_t v_b_592_ = stack[4].m_num;
lean_object* v___y_593_ = stack[5].m_obj;
lean_object* v_res_614_;
v_res_614_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_588_, v_args_589_, v_val_590_, v_a_591_, v_b_592_, v___y_593_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(lean_object* v_upperBound_615_, lean_object* v_args_616_, lean_object* v_val_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v_b_boxed_622_; lean_object* v_res_623_; 
v_b_boxed_622_ = lean_unbox(v_b_619_);
v_res_623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_615_, v_args_616_, v_val_617_, v_a_618_, v_b_boxed_622_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v_val_617_);
lean_dec_ref(v_args_616_);
lean_dec(v_upperBound_615_);
return v_res_623_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(lean_object* v_as_624_, size_t v_i_625_, size_t v_stop_626_, uint8_t v_b_627_, lean_object* v___y_628_){
_start:
{
uint8_t v_a_631_; lean_object* v___y_636_; uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_625_, v_stop_626_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_array_uget_borrowed(v_as_624_, v_i_625_);
lean_inc(v___x_640_);
v___x_641_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_640_, v___x_639_, v___y_628_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; uint8_t v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v___x_643_ = lean_unbox(v_a_642_);
if (v___x_643_ == 0)
{
lean_dec_ref_known(v___x_641_, 1);
v_a_631_ = v_b_627_;
goto v___jp_630_;
}
else
{
v___y_636_ = v___x_641_;
goto v___jp_635_;
}
}
else
{
v___y_636_ = v___x_641_;
goto v___jp_635_;
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(v_b_627_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
v___jp_630_:
{
size_t v___x_632_; size_t v___x_633_; 
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_625_, v___x_632_);
v_i_625_ = v___x_633_;
v_b_627_ = v_a_631_;
goto _start;
}
v___jp_635_:
{
if (lean_obj_tag(v___y_636_) == 0)
{
lean_object* v_a_637_; uint8_t v___x_638_; 
v_a_637_ = lean_ctor_get(v___y_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___y_636_, 1);
v___x_638_ = lean_unbox(v_a_637_);
lean_dec(v_a_637_);
v_a_631_ = v___x_638_;
goto v___jp_630_;
}
else
{
return v___y_636_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_624_ = stack[0].m_obj;
size_t v_i_625_ = stack[1].m_num;
size_t v_stop_626_ = stack[2].m_num;
uint8_t v_b_627_ = stack[3].m_num;
lean_object* v___y_628_ = stack[4].m_obj;
lean_object* v_res_646_;
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_624_, v_i_625_, v_stop_626_, v_b_627_, v___y_628_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_647_, lean_object* v_i_648_, lean_object* v_stop_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
size_t v_i_boxed_653_; size_t v_stop_boxed_654_; uint8_t v_b_boxed_655_; lean_object* v_res_656_; 
v_i_boxed_653_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_stop_boxed_654_ = lean_unbox_usize(v_stop_649_);
lean_dec(v_stop_649_);
v_b_boxed_655_ = lean_unbox(v_b_650_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_647_, v_i_boxed_653_, v_stop_boxed_654_, v_b_boxed_655_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v_as_647_);
return v_res_656_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(lean_object* v_value_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
switch(lean_obj_tag(v_value_657_))
{
case 2:
{
lean_object* v_struct_664_; lean_object* v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
v_struct_664_ = lean_ctor_get(v_value_657_, 2);
lean_inc(v_struct_664_);
lean_dec_ref_known(v_value_657_, 3);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_struct_664_);
v___x_666_ = 1;
v___x_667_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_665_, v___x_666_, v_a_658_);
return v___x_667_;
}
case 3:
{
lean_object* v_declName_668_; lean_object* v_args_669_; lean_object* v___x_670_; 
v_declName_668_ = lean_ctor_get(v_value_657_, 0);
lean_inc(v_declName_668_);
v_args_669_ = lean_ctor_get(v_value_657_, 2);
lean_inc_ref(v_args_669_);
lean_dec_ref_known(v_value_657_, 3);
v___x_670_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_668_, v_a_662_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_699_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_699_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_699_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_699_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_a_671_) == 0)
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_675_ = 0;
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_array_get_size(v_args_669_);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_681_; 
lean_dec_ref(v_args_669_);
v___x_679_ = lean_box(v___x_675_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_679_);
v___x_681_ = v___x_673_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
uint8_t v___x_683_; 
v___x_683_ = lean_nat_dec_le(v___x_677_, v___x_677_);
if (v___x_683_ == 0)
{
if (v___x_678_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec_ref(v_args_669_);
v___x_684_ = lean_box(v___x_675_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_684_);
v___x_686_ = v___x_673_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
lean_del_object(v___x_673_);
v___x_688_ = ((size_t)0ULL);
v___x_689_ = lean_usize_of_nat(v___x_677_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_669_, v___x_688_, v___x_689_, v___x_675_, v_a_658_);
lean_dec_ref(v_args_669_);
return v___x_690_;
}
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
lean_del_object(v___x_673_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_677_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_669_, v___x_691_, v___x_692_, v___x_675_, v_a_658_);
lean_dec_ref(v_args_669_);
return v___x_693_;
}
}
}
else
{
lean_object* v_val_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; 
lean_del_object(v___x_673_);
v_val_694_ = lean_ctor_get(v_a_671_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_a_671_, 1);
v___x_695_ = lean_array_get_size(v_args_669_);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = 0;
v___x_698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_695_, v_args_669_, v_val_694_, v___x_696_, v___x_697_, v_a_658_);
lean_dec(v_val_694_);
lean_dec_ref(v_args_669_);
return v___x_698_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_args_669_);
v_a_700_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_670_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_670_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
case 4:
{
lean_object* v_fvarId_708_; lean_object* v_args_709_; lean_object* v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v_fvarId_708_ = lean_ctor_get(v_value_657_, 0);
lean_inc(v_fvarId_708_);
v_args_709_ = lean_ctor_get(v_value_657_, 1);
lean_inc_ref(v_args_709_);
lean_dec_ref_known(v_value_657_, 2);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_fvarId_708_);
v___x_711_ = 0;
v___x_712_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_710_, v___x_711_, v_a_658_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_array_get_size(v_args_709_);
v___x_716_ = lean_nat_dec_lt(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_dec_ref(v_args_709_);
return v___x_712_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = lean_nat_dec_le(v___x_715_, v___x_715_);
if (v___x_717_ == 0)
{
if (v___x_716_ == 0)
{
lean_dec_ref(v_args_709_);
return v___x_712_;
}
else
{
size_t v___x_718_; size_t v___x_719_; uint8_t v___x_720_; lean_object* v___x_721_; 
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_715_);
v___x_720_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_709_, v___x_718_, v___x_719_, v___x_720_, v_a_658_);
lean_dec_ref(v_args_709_);
return v___x_721_;
}
}
else
{
size_t v___x_722_; size_t v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; 
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_715_);
v___x_724_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_709_, v___x_722_, v___x_723_, v___x_724_, v_a_658_);
lean_dec_ref(v_args_709_);
return v___x_725_;
}
}
}
default: 
{
uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_value_657_);
v___x_726_ = 0;
v___x_727_ = lean_box(v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_657_ = stack[0].m_obj;
lean_object* v_a_658_ = stack[1].m_obj;
lean_object* v_a_659_ = stack[2].m_obj;
lean_object* v_a_660_ = stack[3].m_obj;
lean_object* v_a_661_ = stack[4].m_obj;
lean_object* v_a_662_ = stack[5].m_obj;
lean_object* v_res_729_;
v_res_729_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
stack->m_obj
 = v_res_729_;
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
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(lean_object* v_env_738_, lean_object* v_value_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
return v___x_746_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_738_ = stack[0].m_obj;
lean_object* v_value_739_ = stack[1].m_obj;
lean_object* v_a_740_ = stack[2].m_obj;
lean_object* v_a_741_ = stack[3].m_obj;
lean_object* v_a_742_ = stack[4].m_obj;
lean_object* v_a_743_ = stack[5].m_obj;
lean_object* v_a_744_ = stack[6].m_obj;
lean_object* v_res_747_;
v_res_747_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_738_, v_value_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(lean_object* v_env_748_, lean_object* v_value_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_748_, v_value_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_env_748_);
return v_res_756_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(lean_object* v_as_757_, size_t v_i_758_, size_t v_stop_759_, uint8_t v_b_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_757_, v_i_758_, v_stop_759_, v_b_760_, v___y_761_);
return v___x_767_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_757_ = stack[0].m_obj;
size_t v_i_758_ = stack[1].m_num;
size_t v_stop_759_ = stack[2].m_num;
uint8_t v_b_760_ = stack[3].m_num;
lean_object* v___y_761_ = stack[4].m_obj;
lean_object* v___y_762_ = stack[5].m_obj;
lean_object* v___y_763_ = stack[6].m_obj;
lean_object* v___y_764_ = stack[7].m_obj;
lean_object* v___y_765_ = stack[8].m_obj;
lean_object* v_res_768_;
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_757_, v_i_758_, v_stop_759_, v_b_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(lean_object* v_as_769_, lean_object* v_i_770_, lean_object* v_stop_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
size_t v_i_boxed_779_; size_t v_stop_boxed_780_; uint8_t v_b_boxed_781_; lean_object* v_res_782_; 
v_i_boxed_779_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_stop_boxed_780_ = lean_unbox_usize(v_stop_771_);
lean_dec(v_stop_771_);
v_b_boxed_781_ = lean_unbox(v_b_772_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_769_, v_i_boxed_779_, v_stop_boxed_780_, v_b_boxed_781_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v_as_769_);
return v_res_782_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(lean_object* v_upperBound_783_, lean_object* v_args_784_, lean_object* v_val_785_, lean_object* v_inst_786_, lean_object* v_R_787_, lean_object* v_a_788_, uint8_t v_b_789_, lean_object* v_c_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_783_, v_args_784_, v_val_785_, v_a_788_, v_b_789_, v___y_791_);
return v___x_797_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_783_ = stack[0].m_obj;
lean_object* v_args_784_ = stack[1].m_obj;
lean_object* v_val_785_ = stack[2].m_obj;
lean_object* v_a_788_ = stack[5].m_obj;
uint8_t v_b_789_ = stack[6].m_num;
lean_object* v___y_791_ = stack[8].m_obj;
lean_object* v___y_792_ = stack[9].m_obj;
lean_object* v___y_793_ = stack[10].m_obj;
lean_object* v___y_794_ = stack[11].m_obj;
lean_object* v___y_795_ = stack[12].m_obj;
lean_object* v_res_798_;
v_res_798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_783_, v_args_784_, v_val_785_, lean_box(0), lean_box(0), v_a_788_, v_b_789_, lean_box(0), v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(lean_object* v_upperBound_799_, lean_object* v_args_800_, lean_object* v_val_801_, lean_object* v_inst_802_, lean_object* v_R_803_, lean_object* v_a_804_, lean_object* v_b_805_, lean_object* v_c_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_b_boxed_813_; lean_object* v_res_814_; 
v_b_boxed_813_ = lean_unbox(v_b_805_);
v_res_814_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_799_, v_args_800_, v_val_801_, v_inst_802_, v_R_803_, v_a_804_, v_b_boxed_813_, v_c_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v_val_801_);
lean_dec_ref(v_args_800_);
lean_dec(v_upperBound_799_);
return v_res_814_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(lean_object* v_as_815_, size_t v_i_816_, size_t v_stop_817_, uint8_t v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_815_, v_i_816_, v_stop_817_, v_b_818_, v___y_819_);
return v___x_825_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_815_ = stack[0].m_obj;
size_t v_i_816_ = stack[1].m_num;
size_t v_stop_817_ = stack[2].m_num;
uint8_t v_b_818_ = stack[3].m_num;
lean_object* v___y_819_ = stack[4].m_obj;
lean_object* v___y_820_ = stack[5].m_obj;
lean_object* v___y_821_ = stack[6].m_obj;
lean_object* v___y_822_ = stack[7].m_obj;
lean_object* v___y_823_ = stack[8].m_obj;
lean_object* v_res_826_;
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_815_, v_i_816_, v_stop_817_, v_b_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_, lean_object* v_b_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_i_boxed_837_; size_t v_stop_boxed_838_; uint8_t v_b_boxed_839_; lean_object* v_res_840_; 
v_i_boxed_837_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_838_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_b_boxed_839_ = lean_unbox(v_b_830_);
v_res_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_827_, v_i_boxed_837_, v_stop_boxed_838_, v_b_boxed_839_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v_as_827_);
return v_res_840_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(lean_object* v_value_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
if (lean_obj_tag(v_value_841_) == 0)
{
lean_object* v_decl_848_; lean_object* v_value_849_; lean_object* v___x_850_; 
v_decl_848_ = lean_ctor_get(v_value_841_, 0);
lean_inc_ref(v_decl_848_);
lean_dec_ref_known(v_value_841_, 1);
v_value_849_ = lean_ctor_get(v_decl_848_, 3);
lean_inc(v_value_849_);
lean_dec_ref(v_decl_848_);
v___x_850_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_849_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_850_;
}
else
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_value_841_);
v___x_851_ = 0;
v___x_852_ = lean_box(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_841_ = stack[0].m_obj;
lean_object* v_a_842_ = stack[1].m_obj;
lean_object* v_a_843_ = stack[2].m_obj;
lean_object* v_a_844_ = stack[3].m_obj;
lean_object* v_a_845_ = stack[4].m_obj;
lean_object* v_a_846_ = stack[5].m_obj;
lean_object* v_res_854_;
v_res_854_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(lean_object* v_value_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
return v_res_862_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(lean_object* v_env_863_, lean_object* v_value_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
return v___x_871_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_863_ = stack[0].m_obj;
lean_object* v_value_864_ = stack[1].m_obj;
lean_object* v_a_865_ = stack[2].m_obj;
lean_object* v_a_866_ = stack[3].m_obj;
lean_object* v_a_867_ = stack[4].m_obj;
lean_object* v_a_868_ = stack[5].m_obj;
lean_object* v_a_869_ = stack[6].m_obj;
lean_object* v_res_872_;
v_res_872_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_863_, v_value_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(lean_object* v_env_873_, lean_object* v_value_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_873_, v_value_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_env_873_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(lean_object* v_a_882_, lean_object* v_b_883_, lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_dec(v_b_883_);
lean_dec(v_a_882_);
return v_x_884_;
}
else
{
lean_object* v_key_885_; lean_object* v_value_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_899_; 
v_key_885_ = lean_ctor_get(v_x_884_, 0);
v_value_886_ = lean_ctor_get(v_x_884_, 1);
v_tail_887_ = lean_ctor_get(v_x_884_, 2);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_899_ == 0)
{
v___x_889_ = v_x_884_;
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_value_886_);
lean_inc(v_key_885_);
lean_dec(v_x_884_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_instBEqFVarId_beq(v_key_885_, v_a_882_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_882_, v_b_883_, v_tail_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 2, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_key_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_value_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v_value_886_);
lean_dec(v_key_885_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v_b_883_);
lean_ctor_set(v___x_889_, 0, v_a_882_);
v___x_897_ = v___x_889_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_882_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_b_883_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_tail_887_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(lean_object* v_m_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_size_903_; lean_object* v_buckets_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_947_; 
v_size_903_ = lean_ctor_get(v_m_900_, 0);
v_buckets_904_ = lean_ctor_get(v_m_900_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_m_900_);
if (v_isSharedCheck_947_ == 0)
{
v___x_906_ = v_m_900_;
v_isShared_907_ = v_isSharedCheck_947_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_buckets_904_);
lean_inc(v_size_903_);
lean_dec(v_m_900_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_947_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v_fold_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v_bkt_921_; uint8_t v___x_922_; 
v___x_908_ = lean_array_get_size(v_buckets_904_);
v___x_909_ = l_Lean_instHashableFVarId_hash(v_a_901_);
v___x_910_ = 32ULL;
v___x_911_ = lean_uint64_shift_right(v___x_909_, v___x_910_);
v_fold_912_ = lean_uint64_xor(v___x_909_, v___x_911_);
v___x_913_ = 16ULL;
v___x_914_ = lean_uint64_shift_right(v_fold_912_, v___x_913_);
v___x_915_ = lean_uint64_xor(v_fold_912_, v___x_914_);
v___x_916_ = lean_uint64_to_usize(v___x_915_);
v___x_917_ = lean_usize_of_nat(v___x_908_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_sub(v___x_917_, v___x_918_);
v___x_920_ = lean_usize_land(v___x_916_, v___x_919_);
v_bkt_921_ = lean_array_uget_borrowed(v_buckets_904_, v___x_920_);
v___x_922_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_901_, v_bkt_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v_size_x27_924_; lean_object* v___x_925_; lean_object* v_buckets_x27_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v_size_x27_924_ = lean_nat_add(v_size_903_, v___x_923_);
lean_dec(v_size_903_);
lean_inc(v_bkt_921_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v_a_901_);
lean_ctor_set(v___x_925_, 1, v_b_902_);
lean_ctor_set(v___x_925_, 2, v_bkt_921_);
v_buckets_x27_926_ = lean_array_uset(v_buckets_904_, v___x_920_, v___x_925_);
v___x_927_ = lean_unsigned_to_nat(4u);
v___x_928_ = lean_nat_mul(v_size_x27_924_, v___x_927_);
v___x_929_ = lean_unsigned_to_nat(3u);
v___x_930_ = lean_nat_div(v___x_928_, v___x_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_array_get_size(v_buckets_x27_926_);
v___x_932_ = lean_nat_dec_le(v___x_930_, v___x_931_);
lean_dec(v___x_930_);
if (v___x_932_ == 0)
{
lean_object* v_val_933_; lean_object* v___x_935_; 
v_val_933_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_926_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_val_933_);
lean_ctor_set(v___x_906_, 0, v_size_x27_924_);
v___x_935_ = v___x_906_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_size_x27_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_val_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v___x_938_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_buckets_x27_926_);
lean_ctor_set(v___x_906_, 0, v_size_x27_924_);
v___x_938_ = v___x_906_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_size_x27_924_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_buckets_x27_926_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v___x_940_; lean_object* v_buckets_x27_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_inc(v_bkt_921_);
v___x_940_ = lean_box(0);
v_buckets_x27_941_ = lean_array_uset(v_buckets_904_, v___x_920_, v___x_940_);
v___x_942_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_901_, v_b_902_, v_bkt_921_);
v___x_943_ = lean_array_uset(v_buckets_x27_941_, v___x_920_, v___x_942_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_943_);
v___x_945_ = v___x_906_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_size_903_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(lean_object* v_a_948_, lean_object* v_x_949_){
_start:
{
if (lean_obj_tag(v_x_949_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_box(0);
return v___x_950_;
}
else
{
lean_object* v_key_951_; lean_object* v_value_952_; lean_object* v_tail_953_; uint8_t v___x_954_; 
v_key_951_ = lean_ctor_get(v_x_949_, 0);
v_value_952_ = lean_ctor_get(v_x_949_, 1);
v_tail_953_ = lean_ctor_get(v_x_949_, 2);
v___x_954_ = l_Lean_instBEqFVarId_beq(v_key_951_, v_a_948_);
if (v___x_954_ == 0)
{
v_x_949_ = v_tail_953_;
goto _start;
}
else
{
lean_object* v___x_956_; 
lean_inc(v_value_952_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_value_952_);
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_957_, lean_object* v_x_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_957_, v_x_958_);
lean_dec(v_x_958_);
lean_dec(v_a_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(lean_object* v_m_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_buckets_962_; lean_object* v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v_fold_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_buckets_962_ = lean_ctor_get(v_m_960_, 1);
v___x_963_ = lean_array_get_size(v_buckets_962_);
v___x_964_ = l_Lean_instHashableFVarId_hash(v_a_961_);
v___x_965_ = 32ULL;
v___x_966_ = lean_uint64_shift_right(v___x_964_, v___x_965_);
v_fold_967_ = lean_uint64_xor(v___x_964_, v___x_966_);
v___x_968_ = 16ULL;
v___x_969_ = lean_uint64_shift_right(v_fold_967_, v___x_968_);
v___x_970_ = lean_uint64_xor(v_fold_967_, v___x_969_);
v___x_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = lean_usize_of_nat(v___x_963_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_sub(v___x_972_, v___x_973_);
v___x_975_ = lean_usize_land(v___x_971_, v___x_974_);
v___x_976_ = lean_array_uget_borrowed(v_buckets_962_, v___x_975_);
v___x_977_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_961_, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(lean_object* v_m_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_m_978_);
return v_res_980_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* v_plannedDecision_981_, lean_object* v_var_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_st_ref_get(v_a_983_);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_985_, v_var_982_);
lean_dec(v___x_985_);
if (lean_obj_tag(v___x_986_) == 1)
{
lean_object* v_val_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1011_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1011_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_val_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1011_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
if (lean_obj_tag(v_val_987_) == 3)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_991_ = lean_st_ref_take(v_a_983_);
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_991_, v_var_982_, v_plannedDecision_981_);
v___x_994_ = lean_st_ref_put(v_a_983_, v___x_993_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
lean_ctor_set(v___x_989_, 0, v___x_992_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_992_);
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
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_987_, v_plannedDecision_981_);
lean_dec(v_plannedDecision_981_);
lean_dec(v_val_987_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_999_ = lean_st_ref_take(v_a_983_);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_box(2);
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_999_, v_var_982_, v___x_1001_);
v___x_1003_ = lean_st_ref_put(v_a_983_, v___x_1002_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
lean_ctor_set(v___x_989_, 0, v___x_1000_);
v___x_1005_ = v___x_989_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_dec(v_var_982_);
v___x_1007_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
lean_ctor_set(v___x_989_, 0, v___x_1007_);
v___x_1009_ = v___x_989_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v___x_986_);
lean_dec(v_var_982_);
lean_dec(v_plannedDecision_981_);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_plannedDecision_981_ = stack[0].m_obj;
lean_object* v_var_982_ = stack[1].m_obj;
lean_object* v_a_983_ = stack[2].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_981_, v_var_982_, v_a_983_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* v_plannedDecision_1015_, lean_object* v_var_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1015_, v_var_1016_, v_a_1017_);
lean_dec(v_a_1017_);
return v_res_1019_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* v_plannedDecision_1020_, lean_object* v_var_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_1020_, v_var_1021_, v_a_1022_);
return v___x_1029_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_plannedDecision_1020_ = stack[0].m_obj;
lean_object* v_var_1021_ = stack[1].m_obj;
lean_object* v_a_1022_ = stack[2].m_obj;
lean_object* v_a_1023_ = stack[3].m_obj;
lean_object* v_a_1024_ = stack[4].m_obj;
lean_object* v_a_1025_ = stack[5].m_obj;
lean_object* v_a_1026_ = stack[6].m_obj;
lean_object* v_a_1027_ = stack[7].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1020_, v_var_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* v_plannedDecision_1031_, lean_object* v_var_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_1031_, v_var_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec(v_a_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(lean_object* v_00_u03b2_1041_, lean_object* v_m_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_1042_, v_a_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(lean_object* v_00_u03b2_1045_, lean_object* v_m_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_1045_, v_m_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_m_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(lean_object* v_00_u03b2_1049_, lean_object* v_m_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_1050_, v_a_1051_, v_b_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(lean_object* v_00_u03b2_1054_, lean_object* v_a_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_1058_, v_a_1059_, v_x_1060_);
lean_dec(v_x_1060_);
lean_dec(v_a_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(lean_object* v_00_u03b2_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_1063_, v_b_1064_, v_x_1065_);
return v___x_1066_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(lean_object* v_alt_1067_, lean_object* v_f_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
switch(lean_obj_tag(v_alt_1067_))
{
case 0:
{
lean_object* v_code_1076_; lean_object* v___x_1077_; 
v_code_1076_ = lean_ctor_get(v_alt_1067_, 2);
lean_inc_ref(v_code_1076_);
lean_dec_ref_known(v_alt_1067_, 3);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc_ref(v___y_1071_);
lean_inc(v___y_1070_);
lean_inc(v___y_1069_);
v___x_1077_ = lean_apply_8(v_f_1068_, v_code_1076_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, lean_box(0));
return v___x_1077_;
}
case 1:
{
lean_object* v_code_1078_; lean_object* v___x_1079_; 
v_code_1078_ = lean_ctor_get(v_alt_1067_, 1);
lean_inc_ref(v_code_1078_);
lean_dec_ref_known(v_alt_1067_, 2);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc_ref(v___y_1071_);
lean_inc(v___y_1070_);
lean_inc(v___y_1069_);
v___x_1079_ = lean_apply_8(v_f_1068_, v_code_1078_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, lean_box(0));
return v___x_1079_;
}
default: 
{
lean_object* v_code_1080_; lean_object* v___x_1081_; 
v_code_1080_ = lean_ctor_get(v_alt_1067_, 0);
lean_inc_ref(v_code_1080_);
lean_dec_ref_known(v_alt_1067_, 1);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc(v___y_1072_);
lean_inc_ref(v___y_1071_);
lean_inc(v___y_1070_);
lean_inc(v___y_1069_);
v___x_1081_ = lean_apply_8(v_f_1068_, v_code_1080_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, lean_box(0));
return v___x_1081_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_1067_ = stack[0].m_obj;
lean_object* v_f_1068_ = stack[1].m_obj;
lean_object* v___y_1069_ = stack[2].m_obj;
lean_object* v___y_1070_ = stack[3].m_obj;
lean_object* v___y_1071_ = stack[4].m_obj;
lean_object* v___y_1072_ = stack[5].m_obj;
lean_object* v___y_1073_ = stack[6].m_obj;
lean_object* v___y_1074_ = stack[7].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1067_, v_f_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(lean_object* v_alt_1083_, lean_object* v_f_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1083_, v_f_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
return v_res_1092_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_instMonadEIO___redArg();
return v___x_1093_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(lean_object* v_msg_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_toApplicative_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1171_; 
v___x_1106_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_1107_ = l_StateRefT_x27_instMonad___redArg(v___x_1106_);
v_toApplicative_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v___x_1107_, 1);
lean_dec(v_unused_1172_);
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1171_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_toApplicative_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1171_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_toFunctor_1112_; lean_object* v_toSeq_1113_; lean_object* v_toSeqLeft_1114_; lean_object* v_toSeqRight_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1169_; 
v_toFunctor_1112_ = lean_ctor_get(v_toApplicative_1108_, 0);
v_toSeq_1113_ = lean_ctor_get(v_toApplicative_1108_, 2);
v_toSeqLeft_1114_ = lean_ctor_get(v_toApplicative_1108_, 3);
v_toSeqRight_1115_ = lean_ctor_get(v_toApplicative_1108_, 4);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_toApplicative_1108_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_toApplicative_1108_, 1);
lean_dec(v_unused_1170_);
v___x_1117_ = v_toApplicative_1108_;
v_isShared_1118_ = v_isSharedCheck_1169_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_toSeqRight_1115_);
lean_inc(v_toSeqLeft_1114_);
lean_inc(v_toSeq_1113_);
lean_inc(v_toFunctor_1112_);
lean_dec(v_toApplicative_1108_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1169_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___x_1128_; 
v___f_1119_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_1120_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1112_);
v___f_1121_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1121_, 0, v_toFunctor_1112_);
v___f_1122_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1122_, 0, v_toFunctor_1112_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___f_1121_);
lean_ctor_set(v___x_1123_, 1, v___f_1122_);
v___f_1124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1124_, 0, v_toSeqRight_1115_);
v___f_1125_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1125_, 0, v_toSeqLeft_1114_);
v___f_1126_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1126_, 0, v_toSeq_1113_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 4, v___f_1124_);
lean_ctor_set(v___x_1117_, 3, v___f_1125_);
lean_ctor_set(v___x_1117_, 2, v___f_1126_);
lean_ctor_set(v___x_1117_, 1, v___f_1119_);
lean_ctor_set(v___x_1117_, 0, v___x_1123_);
v___x_1128_ = v___x_1117_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___f_1119_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v___f_1126_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v___f_1125_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v___f_1124_);
v___x_1128_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1130_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v___f_1120_);
lean_ctor_set(v___x_1110_, 0, v___x_1128_);
v___x_1130_ = v___x_1110_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___f_1120_);
v___x_1130_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v_toApplicative_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1165_; 
v___x_1131_ = l_StateRefT_x27_instMonad___redArg(v___x_1130_);
v_toApplicative_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1131_, 1);
lean_dec(v_unused_1166_);
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1165_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_toApplicative_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1165_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_toFunctor_1136_; lean_object* v_toSeq_1137_; lean_object* v_toSeqLeft_1138_; lean_object* v_toSeqRight_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1163_; 
v_toFunctor_1136_ = lean_ctor_get(v_toApplicative_1132_, 0);
v_toSeq_1137_ = lean_ctor_get(v_toApplicative_1132_, 2);
v_toSeqLeft_1138_ = lean_ctor_get(v_toApplicative_1132_, 3);
v_toSeqRight_1139_ = lean_ctor_get(v_toApplicative_1132_, 4);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_toApplicative_1132_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_toApplicative_1132_, 1);
lean_dec(v_unused_1164_);
v___x_1141_ = v_toApplicative_1132_;
v_isShared_1142_ = v_isSharedCheck_1163_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_toSeqRight_1139_);
lean_inc(v_toSeqLeft_1138_);
lean_inc(v_toSeq_1137_);
lean_inc(v_toFunctor_1136_);
lean_dec(v_toApplicative_1132_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1163_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___f_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1152_; 
v___f_1143_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_1144_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1136_);
v___f_1145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1145_, 0, v_toFunctor_1136_);
v___f_1146_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1146_, 0, v_toFunctor_1136_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___f_1145_);
lean_ctor_set(v___x_1147_, 1, v___f_1146_);
v___f_1148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1148_, 0, v_toSeqRight_1139_);
v___f_1149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1149_, 0, v_toSeqLeft_1138_);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1150_, 0, v_toSeq_1137_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 4, v___f_1148_);
lean_ctor_set(v___x_1141_, 3, v___f_1149_);
lean_ctor_set(v___x_1141_, 2, v___f_1150_);
lean_ctor_set(v___x_1141_, 1, v___f_1143_);
lean_ctor_set(v___x_1141_, 0, v___x_1147_);
v___x_1152_ = v___x_1141_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___f_1143_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v___f_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v___f_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v___f_1148_);
v___x_1152_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1154_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___f_1144_);
lean_ctor_set(v___x_1134_, 0, v___x_1152_);
v___x_1154_ = v___x_1134_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___f_1144_);
v___x_1154_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_8045__overap_1159_; lean_object* v___x_1160_; 
v___x_1155_ = l_ReaderT_instMonad___redArg(v___x_1154_);
v___x_1156_ = l_StateRefT_x27_instMonad___redArg(v___x_1155_);
v___x_1157_ = lean_box(0);
v___x_1158_ = l_instInhabitedOfMonad___redArg(v___x_1156_, v___x_1157_);
v___x_8045__overap_1159_ = lean_panic_fn_borrowed(v___x_1158_, v_msg_1098_);
lean_dec(v___x_1158_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
lean_inc(v___y_1100_);
lean_inc(v___y_1099_);
v___x_1160_ = lean_apply_7(v___x_8045__overap_1159_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, lean_box(0));
return v___x_1160_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1098_ = stack[0].m_obj;
lean_object* v___y_1099_ = stack[1].m_obj;
lean_object* v___y_1100_ = stack[2].m_obj;
lean_object* v___y_1101_ = stack[3].m_obj;
lean_object* v___y_1102_ = stack[4].m_obj;
lean_object* v___y_1103_ = stack[5].m_obj;
lean_object* v___y_1104_ = stack[6].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec(v___y_1175_);
return v_res_1182_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2));
v___x_1187_ = lean_unsigned_to_nat(40u);
v___x_1188_ = lean_unsigned_to_nat(49u);
v___x_1189_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1));
v___x_1190_ = ((lean_object*)(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0));
v___x_1191_ = l_mkPanicMessageWithDecl(v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_);
return v___x_1191_;
}
}
lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* v_f_1192_, lean_object* v_e_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_ty_1202_; lean_object* v_body_1203_; uint8_t v___x_1206_; 
v___x_1206_ = l_Lean_Expr_hasFVar(v_e_1193_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_f_1192_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
else
{
switch(lean_obj_tag(v_e_1193_))
{
case 1:
{
lean_object* v_fvarId_1209_; lean_object* v___x_1210_; 
v_fvarId_1209_ = lean_ctor_get(v_e_1193_, 0);
lean_inc(v_fvarId_1209_);
lean_dec_ref_known(v_e_1193_, 1);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
lean_inc(v___y_1194_);
v___x_1210_ = lean_apply_8(v_f_1192_, v_fvarId_1209_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, lean_box(0));
return v___x_1210_;
}
case 2:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref_known(v_e_1193_, 1);
lean_dec_ref(v_f_1192_);
v___x_1211_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1212_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1211_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1212_;
}
case 5:
{
lean_object* v_fn_1213_; lean_object* v_arg_1214_; lean_object* v___x_1215_; 
v_fn_1213_ = lean_ctor_get(v_e_1193_, 0);
lean_inc_ref(v_fn_1213_);
v_arg_1214_ = lean_ctor_get(v_e_1193_, 1);
lean_inc_ref(v_arg_1214_);
lean_dec_ref_known(v_e_1193_, 2);
lean_inc_ref(v_f_1192_);
v___x_1215_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1192_, v_fn_1213_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec_ref_known(v___x_1215_, 1);
v_e_1193_ = v_arg_1214_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1214_);
lean_dec_ref(v_f_1192_);
return v___x_1215_;
}
}
case 6:
{
lean_object* v_binderType_1217_; lean_object* v_body_1218_; 
v_binderType_1217_ = lean_ctor_get(v_e_1193_, 1);
lean_inc_ref(v_binderType_1217_);
v_body_1218_ = lean_ctor_get(v_e_1193_, 2);
lean_inc_ref(v_body_1218_);
lean_dec_ref_known(v_e_1193_, 3);
v_ty_1202_ = v_binderType_1217_;
v_body_1203_ = v_body_1218_;
goto v___jp_1201_;
}
case 7:
{
lean_object* v_binderType_1219_; lean_object* v_body_1220_; 
v_binderType_1219_ = lean_ctor_get(v_e_1193_, 1);
lean_inc_ref(v_binderType_1219_);
v_body_1220_ = lean_ctor_get(v_e_1193_, 2);
lean_inc_ref(v_body_1220_);
lean_dec_ref_known(v_e_1193_, 3);
v_ty_1202_ = v_binderType_1219_;
v_body_1203_ = v_body_1220_;
goto v___jp_1201_;
}
case 8:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref_known(v_e_1193_, 4);
lean_dec_ref(v_f_1192_);
v___x_1221_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1222_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1221_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1222_;
}
case 11:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref_known(v_e_1193_, 3);
lean_dec_ref(v_f_1192_);
v___x_1223_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_1224_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_1223_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1224_;
}
default: 
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_f_1192_);
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
v___jp_1201_:
{
lean_object* v___x_1204_; 
lean_inc_ref(v_f_1192_);
v___x_1204_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1192_, v_ty_1202_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_dec_ref_known(v___x_1204_, 1);
v_e_1193_ = v_body_1203_;
goto _start;
}
else
{
lean_dec_ref(v_body_1203_);
lean_dec_ref(v_f_1192_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1192_ = stack[0].m_obj;
lean_object* v_e_1193_ = stack[1].m_obj;
lean_object* v___y_1194_ = stack[2].m_obj;
lean_object* v___y_1195_ = stack[3].m_obj;
lean_object* v___y_1196_ = stack[4].m_obj;
lean_object* v___y_1197_ = stack[5].m_obj;
lean_object* v___y_1198_ = stack[6].m_obj;
lean_object* v___y_1199_ = stack[7].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1192_, v_e_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(lean_object* v_f_1228_, lean_object* v_e_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1228_, v_e_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
return v_res_1237_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(lean_object* v_f_1238_, lean_object* v_param_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_type_1247_; lean_object* v___x_1248_; 
v_type_1247_ = lean_ctor_get(v_param_1239_, 2);
lean_inc_ref(v_type_1247_);
lean_dec_ref(v_param_1239_);
v___x_1248_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1238_, v_type_1247_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1248_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1238_ = stack[0].m_obj;
lean_object* v_param_1239_ = stack[1].m_obj;
lean_object* v___y_1240_ = stack[2].m_obj;
lean_object* v___y_1241_ = stack[3].m_obj;
lean_object* v___y_1242_ = stack[4].m_obj;
lean_object* v___y_1243_ = stack[5].m_obj;
lean_object* v___y_1244_ = stack[6].m_obj;
lean_object* v___y_1245_ = stack[7].m_obj;
lean_object* v_res_1249_;
v_res_1249_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1238_, v_param_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
stack->m_obj
 = v_res_1249_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(lean_object* v_f_1250_, lean_object* v_param_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1250_, v_param_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v___y_1252_);
return v_res_1259_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(uint8_t v_pu_1260_, lean_object* v_f_1261_, lean_object* v_as_1262_, size_t v_i_1263_, size_t v_stop_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_eq(v_i_1263_, v_stop_1264_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_array_uget_borrowed(v_as_1262_, v_i_1263_);
lean_inc(v___x_1274_);
lean_inc_ref(v_f_1261_);
v___x_1275_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1261_, v___x_1274_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; size_t v___x_1277_; size_t v___x_1278_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_add(v_i_1263_, v___x_1277_);
v_i_1263_ = v___x_1278_;
v_b_1265_ = v_a_1276_;
goto _start;
}
else
{
lean_dec_ref(v_f_1261_);
return v___x_1275_;
}
}
else
{
lean_object* v___x_1280_; 
lean_dec_ref(v_f_1261_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_b_1265_);
return v___x_1280_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1260_ = stack[0].m_num;
lean_object* v_f_1261_ = stack[1].m_obj;
lean_object* v_as_1262_ = stack[2].m_obj;
size_t v_i_1263_ = stack[3].m_num;
size_t v_stop_1264_ = stack[4].m_num;
lean_object* v_b_1265_ = stack[5].m_obj;
lean_object* v___y_1266_ = stack[6].m_obj;
lean_object* v___y_1267_ = stack[7].m_obj;
lean_object* v___y_1268_ = stack[8].m_obj;
lean_object* v___y_1269_ = stack[9].m_obj;
lean_object* v___y_1270_ = stack[10].m_obj;
lean_object* v___y_1271_ = stack[11].m_obj;
lean_object* v_res_1281_;
v_res_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1260_, v_f_1261_, v_as_1262_, v_i_1263_, v_stop_1264_, v_b_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
stack->m_obj
 = v_res_1281_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(lean_object* v_pu_1282_, lean_object* v_f_1283_, lean_object* v_as_1284_, lean_object* v_i_1285_, lean_object* v_stop_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v_pu_boxed_1295_; size_t v_i_boxed_1296_; size_t v_stop_boxed_1297_; lean_object* v_res_1298_; 
v_pu_boxed_1295_ = lean_unbox(v_pu_1282_);
v_i_boxed_1296_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_stop_boxed_1297_ = lean_unbox_usize(v_stop_1286_);
lean_dec(v_stop_1286_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_1295_, v_f_1283_, v_as_1284_, v_i_boxed_1296_, v_stop_boxed_1297_, v_b_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v_as_1284_);
return v_res_1298_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(lean_object* v_f_1299_, lean_object* v_arg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
switch(lean_obj_tag(v_arg_1300_))
{
case 0:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec_ref(v_f_1299_);
v___x_1308_ = lean_box(0);
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
return v___x_1309_;
}
case 1:
{
lean_object* v_fvarId_1310_; lean_object* v___x_1311_; 
v_fvarId_1310_ = lean_ctor_get(v_arg_1300_, 0);
lean_inc(v_fvarId_1310_);
lean_dec_ref_known(v_arg_1300_, 1);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc(v___y_1301_);
v___x_1311_ = lean_apply_8(v_f_1299_, v_fvarId_1310_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
return v___x_1311_;
}
default: 
{
lean_object* v_expr_1312_; lean_object* v___x_1313_; 
v_expr_1312_ = lean_ctor_get(v_arg_1300_, 0);
lean_inc_ref(v_expr_1312_);
lean_dec_ref_known(v_arg_1300_, 1);
v___x_1313_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1299_, v_expr_1312_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1313_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1299_ = stack[0].m_obj;
lean_object* v_arg_1300_ = stack[1].m_obj;
lean_object* v___y_1301_ = stack[2].m_obj;
lean_object* v___y_1302_ = stack[3].m_obj;
lean_object* v___y_1303_ = stack[4].m_obj;
lean_object* v___y_1304_ = stack[5].m_obj;
lean_object* v___y_1305_ = stack[6].m_obj;
lean_object* v___y_1306_ = stack[7].m_obj;
lean_object* v_res_1314_;
v_res_1314_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1299_, v_arg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
stack->m_obj
 = v_res_1314_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(lean_object* v_f_1315_, lean_object* v_arg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1315_, v_arg_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec(v___y_1317_);
return v_res_1324_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(uint8_t v_pu_1325_, lean_object* v_f_1326_, lean_object* v_as_1327_, size_t v_i_1328_, size_t v_stop_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_eq(v_i_1328_, v_stop_1329_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_array_uget_borrowed(v_as_1327_, v_i_1328_);
lean_inc(v___x_1339_);
lean_inc_ref(v_f_1326_);
v___x_1340_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1326_, v___x_1339_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; size_t v___x_1342_; size_t v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1328_, v___x_1342_);
v_i_1328_ = v___x_1343_;
v_b_1330_ = v_a_1341_;
goto _start;
}
else
{
lean_dec_ref(v_f_1326_);
return v___x_1340_;
}
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v_f_1326_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_b_1330_);
return v___x_1345_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1325_ = stack[0].m_num;
lean_object* v_f_1326_ = stack[1].m_obj;
lean_object* v_as_1327_ = stack[2].m_obj;
size_t v_i_1328_ = stack[3].m_num;
size_t v_stop_1329_ = stack[4].m_num;
lean_object* v_b_1330_ = stack[5].m_obj;
lean_object* v___y_1331_ = stack[6].m_obj;
lean_object* v___y_1332_ = stack[7].m_obj;
lean_object* v___y_1333_ = stack[8].m_obj;
lean_object* v___y_1334_ = stack[9].m_obj;
lean_object* v___y_1335_ = stack[10].m_obj;
lean_object* v___y_1336_ = stack[11].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1325_, v_f_1326_, v_as_1327_, v_i_1328_, v_stop_1329_, v_b_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(lean_object* v_pu_1347_, lean_object* v_f_1348_, lean_object* v_as_1349_, lean_object* v_i_1350_, lean_object* v_stop_1351_, lean_object* v_b_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_pu_boxed_1360_; size_t v_i_boxed_1361_; size_t v_stop_boxed_1362_; lean_object* v_res_1363_; 
v_pu_boxed_1360_ = lean_unbox(v_pu_1347_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_stop_boxed_1362_ = lean_unbox_usize(v_stop_1351_);
lean_dec(v_stop_1351_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_1360_, v_f_1348_, v_as_1349_, v_i_boxed_1361_, v_stop_boxed_1362_, v_b_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v_as_1349_);
return v_res_1363_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(uint8_t v_pu_1364_, lean_object* v_f_1365_, lean_object* v_e_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_args_1375_; 
switch(lean_obj_tag(v_e_1366_))
{
case 2:
{
lean_object* v_struct_1384_; lean_object* v___x_1385_; 
v_struct_1384_ = lean_ctor_get(v_e_1366_, 2);
lean_inc(v_struct_1384_);
lean_dec_ref_known(v_e_1366_, 3);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1385_ = lean_apply_8(v_f_1365_, v_struct_1384_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1385_;
}
case 3:
{
lean_object* v_args_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_args_1386_ = lean_ctor_get(v_e_1366_, 2);
lean_inc_ref(v_args_1386_);
lean_dec_ref_known(v_e_1366_, 3);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_array_get_size(v_args_1386_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_nat_dec_lt(v___x_1387_, v___x_1388_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref(v_args_1386_);
lean_dec_ref(v_f_1365_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
return v___x_1391_;
}
else
{
size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = lean_usize_of_nat(v___x_1388_);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1364_, v_f_1365_, v_args_1386_, v___x_1392_, v___x_1393_, v___x_1389_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_args_1386_);
return v___x_1394_;
}
}
case 4:
{
lean_object* v_fvarId_1395_; lean_object* v_args_1396_; lean_object* v___x_1397_; 
v_fvarId_1395_ = lean_ctor_get(v_e_1366_, 0);
lean_inc(v_fvarId_1395_);
v_args_1396_ = lean_ctor_get(v_e_1366_, 1);
lean_inc_ref(v_args_1396_);
lean_dec_ref_known(v_e_1366_, 2);
lean_inc_ref(v_f_1365_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1397_ = lean_apply_8(v_f_1365_, v_fvarId_1395_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1411_; 
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1397_, 0);
lean_dec(v_unused_1412_);
v___x_1399_ = v___x_1397_;
v_isShared_1400_ = v_isSharedCheck_1411_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v___x_1397_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1411_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_array_get_size(v_args_1396_);
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_nat_dec_lt(v___x_1401_, v___x_1402_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_args_1396_);
lean_dec_ref(v_f_1365_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1403_);
v___x_1406_ = v___x_1399_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1403_);
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
lean_del_object(v___x_1399_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1402_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1364_, v_f_1365_, v_args_1396_, v___x_1408_, v___x_1409_, v___x_1403_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_args_1396_);
return v___x_1410_;
}
}
}
else
{
lean_dec_ref(v_args_1396_);
lean_dec_ref(v_f_1365_);
return v___x_1397_;
}
}
case 5:
{
lean_object* v_args_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_args_1413_ = lean_ctor_get(v_e_1366_, 1);
lean_inc_ref(v_args_1413_);
lean_dec_ref_known(v_e_1366_, 2);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_args_1413_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_args_1413_);
lean_dec_ref(v_f_1365_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
return v___x_1418_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1415_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1364_, v_f_1365_, v_args_1413_, v___x_1419_, v___x_1420_, v___x_1416_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_args_1413_);
return v___x_1421_;
}
}
case 6:
{
lean_object* v_var_1422_; lean_object* v___x_1423_; 
v_var_1422_ = lean_ctor_get(v_e_1366_, 1);
lean_inc(v_var_1422_);
lean_dec_ref_known(v_e_1366_, 2);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1423_ = lean_apply_8(v_f_1365_, v_var_1422_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1423_;
}
case 7:
{
lean_object* v_var_1424_; lean_object* v___x_1425_; 
v_var_1424_ = lean_ctor_get(v_e_1366_, 1);
lean_inc(v_var_1424_);
lean_dec_ref_known(v_e_1366_, 2);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1425_ = lean_apply_8(v_f_1365_, v_var_1424_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1425_;
}
case 8:
{
lean_object* v_var_1426_; lean_object* v___x_1427_; 
v_var_1426_ = lean_ctor_get(v_e_1366_, 2);
lean_inc(v_var_1426_);
lean_dec_ref_known(v_e_1366_, 3);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1427_ = lean_apply_8(v_f_1365_, v_var_1426_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1427_;
}
case 9:
{
lean_object* v_args_1428_; 
v_args_1428_ = lean_ctor_get(v_e_1366_, 1);
lean_inc_ref(v_args_1428_);
lean_dec_ref_known(v_e_1366_, 2);
v_args_1375_ = v_args_1428_;
goto v___jp_1374_;
}
case 10:
{
lean_object* v_args_1429_; 
v_args_1429_ = lean_ctor_get(v_e_1366_, 1);
lean_inc_ref(v_args_1429_);
lean_dec_ref_known(v_e_1366_, 2);
v_args_1375_ = v_args_1429_;
goto v___jp_1374_;
}
case 11:
{
lean_object* v_var_1430_; lean_object* v___x_1431_; 
v_var_1430_ = lean_ctor_get(v_e_1366_, 1);
lean_inc(v_var_1430_);
lean_dec_ref_known(v_e_1366_, 2);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1431_ = lean_apply_8(v_f_1365_, v_var_1430_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1431_;
}
case 12:
{
lean_object* v_var_1432_; lean_object* v_args_1433_; lean_object* v___x_1434_; 
v_var_1432_ = lean_ctor_get(v_e_1366_, 0);
lean_inc(v_var_1432_);
v_args_1433_ = lean_ctor_get(v_e_1366_, 2);
lean_inc_ref(v_args_1433_);
lean_dec_ref_known(v_e_1366_, 3);
lean_inc_ref(v_f_1365_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1434_ = lean_apply_8(v_f_1365_, v_var_1432_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1434_, 0);
lean_dec(v_unused_1449_);
v___x_1436_ = v___x_1434_;
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v___x_1434_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_array_get_size(v_args_1433_);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_nat_dec_lt(v___x_1438_, v___x_1439_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1443_; 
lean_dec_ref(v_args_1433_);
lean_dec_ref(v_f_1365_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1440_);
v___x_1443_ = v___x_1436_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1440_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
else
{
size_t v___x_1445_; size_t v___x_1446_; lean_object* v___x_1447_; 
lean_del_object(v___x_1436_);
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = lean_usize_of_nat(v___x_1439_);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1364_, v_f_1365_, v_args_1433_, v___x_1445_, v___x_1446_, v___x_1440_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_args_1433_);
return v___x_1447_;
}
}
}
else
{
lean_dec_ref(v_args_1433_);
lean_dec_ref(v_f_1365_);
return v___x_1434_;
}
}
case 13:
{
lean_object* v_fvarId_1450_; lean_object* v___x_1451_; 
v_fvarId_1450_ = lean_ctor_get(v_e_1366_, 1);
lean_inc(v_fvarId_1450_);
lean_dec_ref_known(v_e_1366_, 2);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1451_ = lean_apply_8(v_f_1365_, v_fvarId_1450_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1451_;
}
case 14:
{
lean_object* v_fvarId_1452_; lean_object* v___x_1453_; 
v_fvarId_1452_ = lean_ctor_get(v_e_1366_, 0);
lean_inc(v_fvarId_1452_);
lean_dec_ref_known(v_e_1366_, 1);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1453_ = lean_apply_8(v_f_1365_, v_fvarId_1452_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1453_;
}
case 15:
{
lean_object* v_fvarId_1454_; lean_object* v___x_1455_; 
v_fvarId_1454_ = lean_ctor_get(v_e_1366_, 0);
lean_inc(v_fvarId_1454_);
lean_dec_ref_known(v_e_1366_, 1);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc(v___y_1367_);
v___x_1455_ = lean_apply_8(v_f_1365_, v_fvarId_1454_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1455_;
}
default: 
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec(v_e_1366_);
lean_dec_ref(v_f_1365_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_args_1375_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref(v_args_1375_);
lean_dec_ref(v_f_1365_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
return v___x_1380_;
}
else
{
size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = lean_usize_of_nat(v___x_1377_);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1364_, v_f_1365_, v_args_1375_, v___x_1381_, v___x_1382_, v___x_1378_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_args_1375_);
return v___x_1383_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1364_ = stack[0].m_num;
lean_object* v_f_1365_ = stack[1].m_obj;
lean_object* v_e_1366_ = stack[2].m_obj;
lean_object* v___y_1367_ = stack[3].m_obj;
lean_object* v___y_1368_ = stack[4].m_obj;
lean_object* v___y_1369_ = stack[5].m_obj;
lean_object* v___y_1370_ = stack[6].m_obj;
lean_object* v___y_1371_ = stack[7].m_obj;
lean_object* v___y_1372_ = stack[8].m_obj;
lean_object* v_res_1458_;
v_res_1458_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1364_, v_f_1365_, v_e_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
stack->m_obj
 = v_res_1458_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(lean_object* v_pu_1459_, lean_object* v_f_1460_, lean_object* v_e_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_pu_boxed_1469_; lean_object* v_res_1470_; 
v_pu_boxed_1469_ = lean_unbox(v_pu_1459_);
v_res_1470_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_1469_, v_f_1460_, v_e_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1470_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(uint8_t v_pu_1471_, lean_object* v_f_1472_, lean_object* v_decl_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_type_1481_; lean_object* v_value_1482_; lean_object* v___x_1483_; 
v_type_1481_ = lean_ctor_get(v_decl_1473_, 2);
lean_inc_ref(v_type_1481_);
v_value_1482_ = lean_ctor_get(v_decl_1473_, 3);
lean_inc(v_value_1482_);
lean_dec_ref(v_decl_1473_);
lean_inc_ref(v_f_1472_);
v___x_1483_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1472_, v_type_1481_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; 
lean_dec_ref_known(v___x_1483_, 1);
v___x_1484_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_1471_, v_f_1472_, v_value_1482_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1484_;
}
else
{
lean_dec(v_value_1482_);
lean_dec_ref(v_f_1472_);
return v___x_1483_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1471_ = stack[0].m_num;
lean_object* v_f_1472_ = stack[1].m_obj;
lean_object* v_decl_1473_ = stack[2].m_obj;
lean_object* v___y_1474_ = stack[3].m_obj;
lean_object* v___y_1475_ = stack[4].m_obj;
lean_object* v___y_1476_ = stack[5].m_obj;
lean_object* v___y_1477_ = stack[6].m_obj;
lean_object* v___y_1478_ = stack[7].m_obj;
lean_object* v___y_1479_ = stack[8].m_obj;
lean_object* v_res_1485_;
v_res_1485_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1471_, v_f_1472_, v_decl_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
stack->m_obj
 = v_res_1485_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(lean_object* v_pu_1486_, lean_object* v_f_1487_, lean_object* v_decl_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v_pu_boxed_1496_; lean_object* v_res_1497_; 
v_pu_boxed_1496_ = lean_unbox(v_pu_1486_);
v_res_1497_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_1496_, v_f_1487_, v_decl_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(lean_object* v_pu_1498_, lean_object* v_f_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v_pu_boxed_1508_; lean_object* v_res_1509_; 
v_pu_boxed_1508_ = lean_unbox(v_pu_1498_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_1508_, v_f_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v___y_1501_);
return v_res_1509_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(uint8_t v_pu_1510_, lean_object* v_f_1511_, lean_object* v_as_1512_, size_t v_i_1513_, size_t v_stop_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_usize_dec_eq(v_i_1513_, v_stop_1514_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = lean_box(v_pu_1510_);
lean_inc_ref(v_f_1511_);
v___f_1525_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1525_, 0, v___x_1524_);
lean_closure_set(v___f_1525_, 1, v_f_1511_);
v___x_1526_ = lean_array_uget_borrowed(v_as_1512_, v_i_1513_);
lean_inc(v___x_1526_);
v___x_1527_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_1526_, v___f_1525_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; size_t v___x_1529_; size_t v___x_1530_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = ((size_t)1ULL);
v___x_1530_ = lean_usize_add(v_i_1513_, v___x_1529_);
v_i_1513_ = v___x_1530_;
v_b_1515_ = v_a_1528_;
goto _start;
}
else
{
lean_dec_ref(v_f_1511_);
return v___x_1527_;
}
}
else
{
lean_object* v___x_1532_; 
lean_dec_ref(v_f_1511_);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_b_1515_);
return v___x_1532_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1510_ = stack[0].m_num;
lean_object* v_f_1511_ = stack[1].m_obj;
lean_object* v_as_1512_ = stack[2].m_obj;
size_t v_i_1513_ = stack[3].m_num;
size_t v_stop_1514_ = stack[4].m_num;
lean_object* v_b_1515_ = stack[5].m_obj;
lean_object* v___y_1516_ = stack[6].m_obj;
lean_object* v___y_1517_ = stack[7].m_obj;
lean_object* v___y_1518_ = stack[8].m_obj;
lean_object* v___y_1519_ = stack[9].m_obj;
lean_object* v___y_1520_ = stack[10].m_obj;
lean_object* v___y_1521_ = stack[11].m_obj;
lean_object* v_res_1533_;
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1510_, v_f_1511_, v_as_1512_, v_i_1513_, v_stop_1514_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
stack->m_obj
 = v_res_1533_;
}
lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(uint8_t v_pu_1534_, lean_object* v_f_1535_, lean_object* v_c_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
switch(lean_obj_tag(v_c_1536_))
{
case 0:
{
lean_object* v_decl_1544_; lean_object* v_k_1545_; lean_object* v___x_1546_; 
v_decl_1544_ = lean_ctor_get(v_c_1536_, 0);
lean_inc_ref(v_decl_1544_);
v_k_1545_ = lean_ctor_get(v_c_1536_, 1);
lean_inc_ref(v_k_1545_);
lean_dec_ref_known(v_c_1536_, 2);
lean_inc_ref(v_f_1535_);
v___x_1546_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_1534_, v_f_1535_, v_decl_1544_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
v_c_1536_ = v_k_1545_;
goto _start;
}
else
{
lean_dec_ref(v_k_1545_);
lean_dec_ref(v_f_1535_);
return v___x_1546_;
}
}
case 3:
{
lean_object* v_fvarId_1548_; lean_object* v_args_1549_; lean_object* v___x_1550_; 
v_fvarId_1548_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1548_);
v_args_1549_ = lean_ctor_get(v_c_1536_, 1);
lean_inc_ref(v_args_1549_);
lean_dec_ref_known(v_c_1536_, 2);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1550_ = lean_apply_8(v_f_1535_, v_fvarId_1548_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1564_; 
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v___x_1550_, 0);
lean_dec(v_unused_1565_);
v___x_1552_ = v___x_1550_;
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v___x_1550_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_array_get_size(v_args_1549_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_nat_dec_lt(v___x_1554_, v___x_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; 
lean_dec_ref(v_args_1549_);
lean_dec_ref(v_f_1535_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1556_);
v___x_1559_ = v___x_1552_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1556_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
lean_del_object(v___x_1552_);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = lean_usize_of_nat(v___x_1555_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_1534_, v_f_1535_, v_args_1549_, v___x_1561_, v___x_1562_, v___x_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v_args_1549_);
return v___x_1563_;
}
}
}
else
{
lean_dec_ref(v_args_1549_);
lean_dec_ref(v_f_1535_);
return v___x_1550_;
}
}
case 4:
{
lean_object* v_cases_1566_; lean_object* v_resultType_1567_; lean_object* v_discr_1568_; lean_object* v_alts_1569_; lean_object* v___x_1570_; 
v_cases_1566_ = lean_ctor_get(v_c_1536_, 0);
lean_inc_ref(v_cases_1566_);
lean_dec_ref_known(v_c_1536_, 1);
v_resultType_1567_ = lean_ctor_get(v_cases_1566_, 1);
lean_inc_ref(v_resultType_1567_);
v_discr_1568_ = lean_ctor_get(v_cases_1566_, 2);
lean_inc(v_discr_1568_);
v_alts_1569_ = lean_ctor_get(v_cases_1566_, 3);
lean_inc_ref(v_alts_1569_);
lean_dec_ref(v_cases_1566_);
lean_inc_ref(v_f_1535_);
v___x_1570_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1535_, v_resultType_1567_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref_known(v___x_1570_, 1);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1571_ = lean_apply_8(v_f_1535_, v_discr_1568_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1585_; 
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1571_, 0);
lean_dec(v_unused_1586_);
v___x_1573_ = v___x_1571_;
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v___x_1571_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_array_get_size(v_alts_1569_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v_alts_1569_);
lean_dec_ref(v_f_1535_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1577_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
lean_del_object(v___x_1573_);
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1576_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_1534_, v_f_1535_, v_alts_1569_, v___x_1582_, v___x_1583_, v___x_1577_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v_alts_1569_);
return v___x_1584_;
}
}
}
else
{
lean_dec_ref(v_alts_1569_);
lean_dec_ref(v_f_1535_);
return v___x_1571_;
}
}
else
{
lean_dec_ref(v_alts_1569_);
lean_dec(v_discr_1568_);
lean_dec_ref(v_f_1535_);
return v___x_1570_;
}
}
case 5:
{
lean_object* v_fvarId_1587_; lean_object* v___x_1588_; 
v_fvarId_1587_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1587_);
lean_dec_ref_known(v_c_1536_, 1);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1588_ = lean_apply_8(v_f_1535_, v_fvarId_1587_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
return v___x_1588_;
}
case 6:
{
lean_object* v_type_1589_; lean_object* v___x_1590_; 
v_type_1589_ = lean_ctor_get(v_c_1536_, 0);
lean_inc_ref(v_type_1589_);
lean_dec_ref_known(v_c_1536_, 1);
v___x_1590_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1535_, v_type_1589_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1590_;
}
case 7:
{
lean_object* v_fvarId_1591_; lean_object* v_y_1592_; lean_object* v_k_1593_; lean_object* v___x_1594_; 
v_fvarId_1591_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1591_);
v_y_1592_ = lean_ctor_get(v_c_1536_, 2);
lean_inc(v_y_1592_);
v_k_1593_ = lean_ctor_get(v_c_1536_, 3);
lean_inc_ref(v_k_1593_);
lean_dec_ref_known(v_c_1536_, 4);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1594_ = lean_apply_8(v_f_1535_, v_fvarId_1591_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
lean_dec_ref_known(v___x_1594_, 1);
lean_inc_ref(v_f_1535_);
v___x_1595_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1535_, v_y_1592_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_dec_ref_known(v___x_1595_, 1);
v_c_1536_ = v_k_1593_;
goto _start;
}
else
{
lean_dec_ref(v_k_1593_);
lean_dec_ref(v_f_1535_);
return v___x_1595_;
}
}
else
{
lean_dec_ref(v_k_1593_);
lean_dec(v_y_1592_);
lean_dec_ref(v_f_1535_);
return v___x_1594_;
}
}
case 8:
{
lean_object* v_fvarId_1597_; lean_object* v_y_1598_; lean_object* v_k_1599_; lean_object* v___x_1600_; 
v_fvarId_1597_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1597_);
v_y_1598_ = lean_ctor_get(v_c_1536_, 2);
lean_inc(v_y_1598_);
v_k_1599_ = lean_ctor_get(v_c_1536_, 3);
lean_inc_ref(v_k_1599_);
lean_dec_ref_known(v_c_1536_, 4);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1600_ = lean_apply_8(v_f_1535_, v_fvarId_1597_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref_known(v___x_1600_, 1);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1601_ = lean_apply_8(v_f_1535_, v_y_1598_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
v_c_1536_ = v_k_1599_;
goto _start;
}
else
{
lean_dec_ref(v_k_1599_);
lean_dec_ref(v_f_1535_);
return v___x_1601_;
}
}
else
{
lean_dec_ref(v_k_1599_);
lean_dec(v_y_1598_);
lean_dec_ref(v_f_1535_);
return v___x_1600_;
}
}
case 9:
{
lean_object* v_fvarId_1603_; lean_object* v_y_1604_; lean_object* v_ty_1605_; lean_object* v_k_1606_; lean_object* v___x_1607_; 
v_fvarId_1603_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1603_);
v_y_1604_ = lean_ctor_get(v_c_1536_, 3);
lean_inc(v_y_1604_);
v_ty_1605_ = lean_ctor_get(v_c_1536_, 4);
lean_inc_ref(v_ty_1605_);
v_k_1606_ = lean_ctor_get(v_c_1536_, 5);
lean_inc_ref(v_k_1606_);
lean_dec_ref_known(v_c_1536_, 6);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1607_ = lean_apply_8(v_f_1535_, v_fvarId_1603_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref_known(v___x_1607_, 1);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1608_ = lean_apply_8(v_f_1535_, v_y_1604_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1608_, 1);
lean_inc_ref(v_f_1535_);
v___x_1609_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1535_, v_ty_1605_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_dec_ref_known(v___x_1609_, 1);
v_c_1536_ = v_k_1606_;
goto _start;
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_f_1535_);
return v___x_1609_;
}
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_ty_1605_);
lean_dec_ref(v_f_1535_);
return v___x_1608_;
}
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_ty_1605_);
lean_dec(v_y_1604_);
lean_dec_ref(v_f_1535_);
return v___x_1607_;
}
}
case 10:
{
lean_object* v_fvarId_1611_; lean_object* v_k_1612_; lean_object* v___x_1613_; 
v_fvarId_1611_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1611_);
v_k_1612_ = lean_ctor_get(v_c_1536_, 2);
lean_inc_ref(v_k_1612_);
lean_dec_ref_known(v_c_1536_, 3);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1613_ = lean_apply_8(v_f_1535_, v_fvarId_1611_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec_ref_known(v___x_1613_, 1);
v_c_1536_ = v_k_1612_;
goto _start;
}
else
{
lean_dec_ref(v_k_1612_);
lean_dec_ref(v_f_1535_);
return v___x_1613_;
}
}
case 11:
{
lean_object* v_fvarId_1615_; lean_object* v_k_1616_; lean_object* v___x_1617_; 
v_fvarId_1615_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1615_);
v_k_1616_ = lean_ctor_get(v_c_1536_, 2);
lean_inc_ref(v_k_1616_);
lean_dec_ref_known(v_c_1536_, 3);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1617_ = lean_apply_8(v_f_1535_, v_fvarId_1615_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec_ref_known(v___x_1617_, 1);
v_c_1536_ = v_k_1616_;
goto _start;
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_f_1535_);
return v___x_1617_;
}
}
case 12:
{
lean_object* v_fvarId_1619_; lean_object* v_k_1620_; lean_object* v___x_1621_; 
v_fvarId_1619_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1619_);
v_k_1620_ = lean_ctor_get(v_c_1536_, 3);
lean_inc_ref(v_k_1620_);
lean_dec_ref_known(v_c_1536_, 4);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1621_ = lean_apply_8(v_f_1535_, v_fvarId_1619_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_dec_ref_known(v___x_1621_, 1);
v_c_1536_ = v_k_1620_;
goto _start;
}
else
{
lean_dec_ref(v_k_1620_);
lean_dec_ref(v_f_1535_);
return v___x_1621_;
}
}
case 13:
{
lean_object* v_fvarId_1623_; lean_object* v_k_1624_; lean_object* v___x_1625_; 
v_fvarId_1623_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_fvarId_1623_);
v_k_1624_ = lean_ctor_get(v_c_1536_, 1);
lean_inc_ref(v_k_1624_);
lean_dec_ref_known(v_c_1536_, 2);
lean_inc_ref(v_f_1535_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc(v___y_1537_);
v___x_1625_ = lean_apply_8(v_f_1535_, v_fvarId_1623_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_dec_ref_known(v___x_1625_, 1);
v_c_1536_ = v_k_1624_;
goto _start;
}
else
{
lean_dec_ref(v_k_1624_);
lean_dec_ref(v_f_1535_);
return v___x_1625_;
}
}
default: 
{
lean_object* v_decl_1627_; lean_object* v_k_1628_; lean_object* v_params_1629_; lean_object* v_type_1630_; lean_object* v_value_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_decl_1627_ = lean_ctor_get(v_c_1536_, 0);
lean_inc_ref(v_decl_1627_);
v_k_1628_ = lean_ctor_get(v_c_1536_, 1);
lean_inc_ref(v_k_1628_);
lean_dec_ref(v_c_1536_);
v_params_1629_ = lean_ctor_get(v_decl_1627_, 2);
lean_inc_ref(v_params_1629_);
v_type_1630_ = lean_ctor_get(v_decl_1627_, 3);
lean_inc_ref(v_type_1630_);
v_value_1631_ = lean_ctor_get(v_decl_1627_, 4);
lean_inc_ref(v_value_1631_);
lean_dec_ref(v_decl_1627_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_array_get_size(v_params_1629_);
v___x_1634_ = lean_nat_dec_lt(v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v_params_1629_);
lean_inc_ref(v_f_1535_);
v___x_1635_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1535_, v_type_1630_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v___x_1635_, 1);
lean_inc_ref(v_f_1535_);
v___x_1636_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1534_, v_f_1535_, v_value_1631_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_dec_ref_known(v___x_1636_, 1);
v_c_1536_ = v_k_1628_;
goto _start;
}
else
{
lean_dec_ref(v_k_1628_);
lean_dec_ref(v_f_1535_);
return v___x_1636_;
}
}
else
{
lean_dec_ref(v_value_1631_);
lean_dec_ref(v_k_1628_);
lean_dec_ref(v_f_1535_);
return v___x_1635_;
}
}
else
{
lean_object* v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_box(0);
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = lean_usize_of_nat(v___x_1633_);
lean_inc_ref(v_f_1535_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_1534_, v_f_1535_, v_params_1629_, v___x_1639_, v___x_1640_, v___x_1638_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v_params_1629_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1642_; 
lean_dec_ref_known(v___x_1641_, 1);
lean_inc_ref(v_f_1535_);
v___x_1642_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_1535_, v_type_1630_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1643_; 
lean_dec_ref_known(v___x_1642_, 1);
lean_inc_ref(v_f_1535_);
v___x_1643_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1534_, v_f_1535_, v_value_1631_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_dec_ref_known(v___x_1643_, 1);
v_c_1536_ = v_k_1628_;
goto _start;
}
else
{
lean_dec_ref(v_k_1628_);
lean_dec_ref(v_f_1535_);
return v___x_1643_;
}
}
else
{
lean_dec_ref(v_value_1631_);
lean_dec_ref(v_k_1628_);
lean_dec_ref(v_f_1535_);
return v___x_1642_;
}
}
else
{
lean_dec_ref(v_value_1631_);
lean_dec_ref(v_type_1630_);
lean_dec_ref(v_k_1628_);
lean_dec_ref(v_f_1535_);
return v___x_1641_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1534_ = stack[0].m_num;
lean_object* v_f_1535_ = stack[1].m_obj;
lean_object* v_c_1536_ = stack[2].m_obj;
lean_object* v___y_1537_ = stack[3].m_obj;
lean_object* v___y_1538_ = stack[4].m_obj;
lean_object* v___y_1539_ = stack[5].m_obj;
lean_object* v___y_1540_ = stack[6].m_obj;
lean_object* v___y_1541_ = stack[7].m_obj;
lean_object* v___y_1542_ = stack[8].m_obj;
lean_object* v_res_1645_;
v_res_1645_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1534_, v_f_1535_, v_c_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
stack->m_obj
 = v_res_1645_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(uint8_t v_pu_1646_, lean_object* v_f_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_1646_, v_f_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1646_ = stack[0].m_num;
lean_object* v_f_1647_ = stack[1].m_obj;
lean_object* v___y_1648_ = stack[2].m_obj;
lean_object* v___y_1649_ = stack[3].m_obj;
lean_object* v___y_1650_ = stack[4].m_obj;
lean_object* v___y_1651_ = stack[5].m_obj;
lean_object* v___y_1652_ = stack[6].m_obj;
lean_object* v___y_1653_ = stack[7].m_obj;
lean_object* v___y_1654_ = stack[8].m_obj;
lean_object* v_res_1657_;
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_1646_, v_f_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
stack->m_obj
 = v_res_1657_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(lean_object* v_pu_1658_, lean_object* v_f_1659_, lean_object* v_as_1660_, lean_object* v_i_1661_, lean_object* v_stop_1662_, lean_object* v_b_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v_pu_boxed_1671_; size_t v_i_boxed_1672_; size_t v_stop_boxed_1673_; lean_object* v_res_1674_; 
v_pu_boxed_1671_ = lean_unbox(v_pu_1658_);
v_i_boxed_1672_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_stop_boxed_1673_ = lean_unbox_usize(v_stop_1662_);
lean_dec(v_stop_1662_);
v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_1671_, v_f_1659_, v_as_1660_, v_i_boxed_1672_, v_stop_boxed_1673_, v_b_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v_as_1660_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(lean_object* v_pu_1675_, lean_object* v_f_1676_, lean_object* v_c_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_pu_boxed_1685_; lean_object* v_res_1686_; 
v_pu_boxed_1685_ = lean_unbox(v_pu_1675_);
v_res_1686_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_1685_, v_f_1676_, v_c_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1686_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(lean_object* v___x_1687_, lean_object* v_as_1688_, size_t v_i_1689_, size_t v_stop_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_eq(v_i_1689_, v_stop_1690_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc(v___x_1687_);
v___x_1700_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1700_, 0, v___x_1687_);
v___x_1701_ = lean_array_uget_borrowed(v_as_1688_, v_i_1689_);
lean_inc(v___x_1701_);
v___x_1702_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_1700_, v___x_1701_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; size_t v___x_1704_; size_t v___x_1705_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1689_, v___x_1704_);
v_i_1689_ = v___x_1705_;
v_b_1691_ = v_a_1703_;
goto _start;
}
else
{
lean_dec(v___x_1687_);
return v___x_1702_;
}
}
else
{
lean_object* v___x_1707_; 
lean_dec(v___x_1687_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_b_1691_);
return v___x_1707_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1687_ = stack[0].m_obj;
lean_object* v_as_1688_ = stack[1].m_obj;
size_t v_i_1689_ = stack[2].m_num;
size_t v_stop_1690_ = stack[3].m_num;
lean_object* v_b_1691_ = stack[4].m_obj;
lean_object* v___y_1692_ = stack[5].m_obj;
lean_object* v___y_1693_ = stack[6].m_obj;
lean_object* v___y_1694_ = stack[7].m_obj;
lean_object* v___y_1695_ = stack[8].m_obj;
lean_object* v___y_1696_ = stack[9].m_obj;
lean_object* v___y_1697_ = stack[10].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1687_, v_as_1688_, v_i_1689_, v_stop_1690_, v_b_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(lean_object* v___x_1709_, lean_object* v_as_1710_, lean_object* v_i_1711_, lean_object* v_stop_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
size_t v_i_boxed_1721_; size_t v_stop_boxed_1722_; lean_object* v_res_1723_; 
v_i_boxed_1721_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_stop_boxed_1722_ = lean_unbox_usize(v_stop_1712_);
lean_dec(v_stop_1712_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1709_, v_as_1710_, v_i_boxed_1721_, v_stop_boxed_1722_, v_b_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v_as_1710_);
return v_res_1723_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* v_alt_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = 0;
v___x_1733_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_1724_);
lean_inc(v___x_1733_);
v___x_1734_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(v___x_1734_, 0, v___x_1733_);
switch(lean_obj_tag(v_alt_1724_))
{
case 0:
{
lean_object* v_params_1735_; lean_object* v_code_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_params_1735_ = lean_ctor_get(v_alt_1724_, 1);
lean_inc_ref(v_params_1735_);
v_code_1736_ = lean_ctor_get(v_alt_1724_, 2);
lean_inc_ref(v_code_1736_);
lean_dec_ref_known(v_alt_1724_, 3);
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_array_get_size(v_params_1735_);
v___x_1739_ = lean_nat_dec_lt(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v_params_1735_);
lean_dec(v___x_1733_);
v___x_1740_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1732_, v___x_1734_, v_code_1736_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1740_;
}
else
{
lean_object* v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = ((size_t)0ULL);
v___x_1743_ = lean_usize_of_nat(v___x_1738_);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_1733_, v_params_1735_, v___x_1742_, v___x_1743_, v___x_1741_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec_ref(v_params_1735_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref_known(v___x_1744_, 1);
v___x_1745_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1732_, v___x_1734_, v_code_1736_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1745_;
}
else
{
lean_dec_ref(v_code_1736_);
lean_dec_ref(v___x_1734_);
return v___x_1744_;
}
}
}
case 1:
{
lean_object* v_code_1746_; lean_object* v___x_1747_; 
lean_dec(v___x_1733_);
v_code_1746_ = lean_ctor_get(v_alt_1724_, 1);
lean_inc_ref(v_code_1746_);
lean_dec_ref_known(v_alt_1724_, 2);
v___x_1747_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1732_, v___x_1734_, v_code_1746_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1747_;
}
default: 
{
lean_object* v_code_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1733_);
v_code_1748_ = lean_ctor_get(v_alt_1724_, 0);
lean_inc_ref(v_code_1748_);
lean_dec_ref_known(v_alt_1724_, 1);
v___x_1749_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_1732_, v___x_1734_, v_code_1748_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_1724_ = stack[0].m_obj;
lean_object* v_a_1725_ = stack[1].m_obj;
lean_object* v_a_1726_ = stack[2].m_obj;
lean_object* v_a_1727_ = stack[3].m_obj;
lean_object* v_a_1728_ = stack[4].m_obj;
lean_object* v_a_1729_ = stack[5].m_obj;
lean_object* v_a_1730_ = stack[6].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
stack->m_obj
 = v_res_1750_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(lean_object* v_alt_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec(v_a_1752_);
return v_res_1759_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(uint8_t v_pu_1760_, lean_object* v_f_1761_, lean_object* v_param_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_1761_, v_param_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1760_ = stack[0].m_num;
lean_object* v_f_1761_ = stack[1].m_obj;
lean_object* v_param_1762_ = stack[2].m_obj;
lean_object* v___y_1763_ = stack[3].m_obj;
lean_object* v___y_1764_ = stack[4].m_obj;
lean_object* v___y_1765_ = stack[5].m_obj;
lean_object* v___y_1766_ = stack[6].m_obj;
lean_object* v___y_1767_ = stack[7].m_obj;
lean_object* v___y_1768_ = stack[8].m_obj;
lean_object* v_res_1771_;
v_res_1771_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_1760_, v_f_1761_, v_param_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
stack->m_obj
 = v_res_1771_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(lean_object* v_pu_1772_, lean_object* v_f_1773_, lean_object* v_param_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
uint8_t v_pu_boxed_1782_; lean_object* v_res_1783_; 
v_pu_boxed_1782_ = lean_unbox(v_pu_1772_);
v_res_1783_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_1782_, v_f_1773_, v_param_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec(v___y_1775_);
return v_res_1783_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(uint8_t v_pu_1784_, lean_object* v_alt_1785_, lean_object* v_f_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_1785_, v_f_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1784_ = stack[0].m_num;
lean_object* v_alt_1785_ = stack[1].m_obj;
lean_object* v_f_1786_ = stack[2].m_obj;
lean_object* v___y_1787_ = stack[3].m_obj;
lean_object* v___y_1788_ = stack[4].m_obj;
lean_object* v___y_1789_ = stack[5].m_obj;
lean_object* v___y_1790_ = stack[6].m_obj;
lean_object* v___y_1791_ = stack[7].m_obj;
lean_object* v___y_1792_ = stack[8].m_obj;
lean_object* v_res_1795_;
v_res_1795_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_1784_, v_alt_1785_, v_f_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
stack->m_obj
 = v_res_1795_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(lean_object* v_pu_1796_, lean_object* v_alt_1797_, lean_object* v_f_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
uint8_t v_pu_boxed_1806_; lean_object* v_res_1807_; 
v_pu_boxed_1806_ = lean_unbox(v_pu_1796_);
v_res_1807_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_1806_, v_alt_1797_, v_f_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec(v___y_1799_);
return v_res_1807_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(uint8_t v_pu_1808_, lean_object* v_f_1809_, lean_object* v_arg_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_1809_, v_arg_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1808_ = stack[0].m_num;
lean_object* v_f_1809_ = stack[1].m_obj;
lean_object* v_arg_1810_ = stack[2].m_obj;
lean_object* v___y_1811_ = stack[3].m_obj;
lean_object* v___y_1812_ = stack[4].m_obj;
lean_object* v___y_1813_ = stack[5].m_obj;
lean_object* v___y_1814_ = stack[6].m_obj;
lean_object* v___y_1815_ = stack[7].m_obj;
lean_object* v___y_1816_ = stack[8].m_obj;
lean_object* v_res_1819_;
v_res_1819_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_1808_, v_f_1809_, v_arg_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
stack->m_obj
 = v_res_1819_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(lean_object* v_pu_1820_, lean_object* v_f_1821_, lean_object* v_arg_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v_pu_boxed_1830_; lean_object* v_res_1831_; 
v_pu_boxed_1830_ = lean_unbox(v_pu_1820_);
v_res_1831_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_1830_, v_f_1821_, v_arg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
return v_res_1831_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* v_as_1832_, size_t v_i_1833_, size_t v_stop_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_usize_dec_eq(v_i_1833_, v_stop_1834_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_array_uget_borrowed(v_as_1832_, v_i_1833_);
lean_inc(v___x_1844_);
v___x_1845_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_1844_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; size_t v___x_1847_; size_t v___x_1848_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = ((size_t)1ULL);
v___x_1848_ = lean_usize_add(v_i_1833_, v___x_1847_);
v_i_1833_ = v___x_1848_;
v_b_1835_ = v_a_1846_;
goto _start;
}
else
{
return v___x_1845_;
}
}
else
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_b_1835_);
return v___x_1850_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1832_ = stack[0].m_obj;
size_t v_i_1833_ = stack[1].m_num;
size_t v_stop_1834_ = stack[2].m_num;
lean_object* v_b_1835_ = stack[3].m_obj;
lean_object* v___y_1836_ = stack[4].m_obj;
lean_object* v___y_1837_ = stack[5].m_obj;
lean_object* v___y_1838_ = stack[6].m_obj;
lean_object* v___y_1839_ = stack[7].m_obj;
lean_object* v___y_1840_ = stack[8].m_obj;
lean_object* v___y_1841_ = stack[9].m_obj;
lean_object* v_res_1851_;
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1832_, v_i_1833_, v_stop_1834_, v_b_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
stack->m_obj
 = v_res_1851_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* v_as_1852_, lean_object* v_i_1853_, lean_object* v_stop_1854_, lean_object* v_b_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
size_t v_i_boxed_1863_; size_t v_stop_boxed_1864_; lean_object* v_res_1865_; 
v_i_boxed_1863_ = lean_unbox_usize(v_i_1853_);
lean_dec(v_i_1853_);
v_stop_boxed_1864_ = lean_unbox_usize(v_stop_1854_);
lean_dec(v_stop_1854_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_1852_, v_i_boxed_1863_, v_stop_boxed_1864_, v_b_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v_as_1852_);
return v_res_1865_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* v_cs_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_alts_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_alts_1874_ = lean_ctor_get(v_cs_1866_, 3);
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_array_get_size(v_alts_1874_);
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_nat_dec_lt(v___x_1875_, v___x_1876_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
return v___x_1879_;
}
else
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_nat_dec_le(v___x_1876_, v___x_1876_);
if (v___x_1880_ == 0)
{
if (v___x_1878_ == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1877_);
return v___x_1881_;
}
else
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = lean_usize_of_nat(v___x_1876_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1874_, v___x_1882_, v___x_1883_, v___x_1877_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1884_;
}
}
else
{
size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = lean_usize_of_nat(v___x_1876_);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_1874_, v___x_1885_, v___x_1886_, v___x_1877_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1887_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_cs_1866_ = stack[0].m_obj;
lean_object* v_a_1867_ = stack[1].m_obj;
lean_object* v_a_1868_ = stack[2].m_obj;
lean_object* v_a_1869_ = stack[3].m_obj;
lean_object* v_a_1870_ = stack[4].m_obj;
lean_object* v_a_1871_ = stack[5].m_obj;
lean_object* v_a_1872_ = stack[6].m_obj;
lean_object* v_res_1888_;
v_res_1888_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
stack->m_obj
 = v_res_1888_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* v_cs_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_cs_1889_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(lean_object* v_as_x27_1898_, lean_object* v_b_1899_){
_start:
{
if (lean_obj_tag(v_as_x27_1898_) == 0)
{
return v_b_1899_;
}
else
{
lean_object* v_head_1900_; lean_object* v_tail_1901_; lean_object* v_fst_1902_; lean_object* v_snd_1903_; lean_object* v_r_1904_; 
v_head_1900_ = lean_ctor_get(v_as_x27_1898_, 0);
v_tail_1901_ = lean_ctor_get(v_as_x27_1898_, 1);
v_fst_1902_ = lean_ctor_get(v_head_1900_, 0);
v_snd_1903_ = lean_ctor_get(v_head_1900_, 1);
lean_inc(v_snd_1903_);
lean_inc(v_fst_1902_);
v_r_1904_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_b_1899_, v_fst_1902_, v_snd_1903_);
v_as_x27_1898_ = v_tail_1901_;
v_b_1899_ = v_r_1904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg___boxed(lean_object* v_as_x27_1906_, lean_object* v_b_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_as_x27_1906_, v_b_1907_);
lean_dec(v_as_x27_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(lean_object* v_m_1909_, lean_object* v_l_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_l_1910_, v_m_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2___boxed(lean_object* v_m_1912_, lean_object* v_l_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2(v_m_1912_, v_l_1913_);
lean_dec(v_l_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = l_List_reverse___redArg(v_a_1916_);
return v___x_1917_;
}
else
{
lean_object* v_head_1918_; lean_object* v_tail_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1930_; 
v_head_1918_ = lean_ctor_get(v_a_1915_, 0);
v_tail_1919_ = lean_ctor_get(v_a_1915_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_a_1915_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1921_ = v_a_1915_;
v_isShared_1922_ = v_isSharedCheck_1930_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_tail_1919_);
lean_inc(v_head_1918_);
lean_dec(v_a_1915_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1930_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1923_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1918_);
lean_dec(v_head_1918_);
v___x_1924_ = lean_box(2);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_a_1916_);
lean_ctor_set(v___x_1921_, 0, v___x_1925_);
v___x_1927_ = v___x_1921_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_a_1916_);
v___x_1927_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v_a_1915_ = v_tail_1919_;
v_a_1916_ = v___x_1927_;
goto _start;
}
}
}
}
}
lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_x_1931_);
return v___x_1938_;
}
else
{
lean_object* v_head_1939_; lean_object* v_tail_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_2002_; 
v_head_1939_ = lean_ctor_get(v_x_1932_, 0);
v_tail_1940_ = lean_ctor_get(v_x_1932_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1942_ = v_x_1932_;
v_isShared_1943_ = v_isSharedCheck_2002_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_tail_1940_);
lean_inc(v_head_1939_);
lean_dec(v_x_1932_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_2002_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_2001_; 
v_fst_1944_ = lean_ctor_get(v_x_1931_, 0);
v_snd_1945_ = lean_ctor_get(v_x_1931_, 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_x_1931_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1947_ = v_x_1931_;
v_isShared_1948_ = v_isSharedCheck_2001_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_snd_1945_);
lean_inc(v_fst_1944_);
lean_dec(v_x_1931_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_2001_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; 
if (lean_obj_tag(v_head_1939_) == 0)
{
lean_object* v_decl_1982_; lean_object* v___x_1983_; 
v_decl_1982_ = lean_ctor_get(v_head_1939_, 0);
lean_inc_ref(v_decl_1982_);
v___x_1983_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(v_decl_1982_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; uint8_t v___x_1985_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = lean_unbox(v_a_1984_);
lean_dec(v_a_1984_);
if (v___x_1985_ == 0)
{
lean_del_object(v___x_1942_);
v___y_1950_ = v___y_1933_;
v___y_1951_ = v___y_1934_;
v___y_1952_ = v___y_1935_;
v___y_1953_ = v___y_1936_;
goto v___jp_1949_;
}
else
{
lean_object* v_fvarId_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_inc_ref(v_decl_1982_);
lean_dec_ref_known(v_head_1939_, 1);
lean_del_object(v___x_1947_);
v_fvarId_1986_ = lean_ctor_get(v_decl_1982_, 0);
lean_inc(v_fvarId_1986_);
lean_dec_ref(v_decl_1982_);
v___x_1987_ = lean_box(2);
v___x_1988_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1944_, v_fvarId_1986_, v___x_1987_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 0);
lean_ctor_set(v___x_1942_, 1, v_snd_1945_);
lean_ctor_set(v___x_1942_, 0, v___x_1988_);
v___x_1990_ = v___x_1942_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_snd_1945_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
v_x_1931_ = v___x_1990_;
v_x_1932_ = v_tail_1940_;
goto _start;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref_known(v_head_1939_, 1);
lean_del_object(v___x_1947_);
lean_dec(v_snd_1945_);
lean_dec(v_fst_1944_);
lean_del_object(v___x_1942_);
lean_dec(v_tail_1940_);
v_a_1993_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1983_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1983_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_del_object(v___x_1942_);
v___y_1950_ = v___y_1933_;
v___y_1951_ = v___y_1934_;
v___y_1952_ = v___y_1935_;
v___y_1953_ = v___y_1936_;
goto v___jp_1949_;
}
v___jp_1949_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_st_ref_get(v___y_1953_);
lean_dec(v___x_1954_);
v___x_1955_ = lean_st_mk_ref(v_snd_1945_);
lean_inc(v_head_1939_);
v___x_1956_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_1939_, v___x_1955_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_st_ref_get(v___x_1955_);
lean_dec(v___x_1955_);
v___x_1959_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1960_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1939_);
lean_dec(v_head_1939_);
v___x_1961_ = lean_box(3);
v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1944_, v___x_1960_, v___x_1961_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v___x_1958_);
lean_ctor_set(v___x_1947_, 0, v___x_1962_);
v___x_1964_ = v___x_1947_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1958_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
v_x_1931_ = v___x_1964_;
v_x_1932_ = v_tail_1940_;
goto _start;
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1967_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_1939_);
lean_dec(v_head_1939_);
v___x_1968_ = lean_box(2);
v___x_1969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_1944_, v___x_1967_, v___x_1968_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v___x_1958_);
lean_ctor_set(v___x_1947_, 0, v___x_1969_);
v___x_1971_ = v___x_1947_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1958_);
v___x_1971_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v_x_1931_ = v___x_1971_;
v_x_1932_ = v_tail_1940_;
goto _start;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v___x_1955_);
lean_del_object(v___x_1947_);
lean_dec(v_fst_1944_);
lean_dec(v_tail_1940_);
lean_dec(v_head_1939_);
v_a_1974_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1956_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1956_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1931_ = stack[0].m_obj;
lean_object* v_x_1932_ = stack[1].m_obj;
lean_object* v___y_1933_ = stack[2].m_obj;
lean_object* v___y_1934_ = stack[3].m_obj;
lean_object* v___y_1935_ = stack[4].m_obj;
lean_object* v___y_1936_ = stack[5].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_1931_, v_x_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
stack->m_obj
 = v_res_2003_;
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
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* v_cs_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_map_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v_typeName_2060_; lean_object* v_discr_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___y_2074_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_typeName_2060_ = lean_ctor_get(v_cs_2027_, 0);
v_discr_2061_ = lean_ctor_get(v_cs_2027_, 2);
v___x_2062_ = l_List_lengthTR___redArg(v_a_2028_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_unsigned_to_nat(4u);
v___x_2065_ = lean_nat_mul(v___x_2062_, v___x_2064_);
lean_dec(v___x_2062_);
v___x_2066_ = lean_unsigned_to_nat(3u);
v___x_2067_ = lean_nat_div(v___x_2065_, v___x_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = l_Nat_nextPowerOfTwo(v___x_2067_);
lean_dec(v___x_2067_);
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_mk_array(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2063_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_obj_once(&l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1, &l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once, _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1);
v___x_2094_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__4));
v___x_2095_ = lean_name_eq(v_typeName_2060_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__6));
v___x_2097_ = lean_name_eq(v_typeName_2060_, v___x_2096_);
v___y_2074_ = v___x_2097_;
goto v___jp_2073_;
}
else
{
v___y_2074_ = v___x_2095_;
goto v___jp_2073_;
}
v___jp_2034_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_st_mk_ref(v_map_2035_);
v___x_2042_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_2027_, v___x_2041_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec_ref(v_cs_2027_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2042_, 0);
lean_dec(v_unused_2051_);
v___x_2044_ = v___x_2042_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v___x_2042_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_st_ref_get(v___x_2041_);
lean_dec(v___x_2041_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v___x_2041_);
v_a_2052_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2042_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2042_);
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
v___jp_2073_:
{
if (v___y_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2071_);
lean_ctor_set(v___x_2075_, 1, v___x_2072_);
lean_inc(v_a_2028_);
v___x_2076_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_2075_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v_fst_2078_; uint8_t v___x_2079_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v_fst_2078_ = lean_ctor_get(v_a_2077_, 0);
lean_inc(v_fst_2078_);
lean_dec(v_a_2077_);
v___x_2079_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_2078_, v_discr_2061_);
if (v___x_2079_ == 0)
{
v_map_2035_ = v_fst_2078_;
v___y_2036_ = v_a_2028_;
v___y_2037_ = v_a_2029_;
v___y_2038_ = v_a_2030_;
v___y_2039_ = v_a_2031_;
v___y_2040_ = v_a_2032_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_box(2);
lean_inc(v_discr_2061_);
v___x_2081_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_2078_, v_discr_2061_, v___x_2080_);
v_map_2035_ = v___x_2081_;
v___y_2036_ = v_a_2028_;
v___y_2037_ = v_a_2029_;
v___y_2038_ = v_a_2030_;
v___y_2039_ = v_a_2031_;
v___y_2040_ = v_a_2032_;
goto v___jp_2034_;
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_cs_2027_);
v_a_2082_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2076_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2076_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref_known(v___x_2071_, 2);
lean_dec_ref(v_cs_2027_);
v___x_2090_ = lean_box(0);
lean_inc(v_a_2028_);
v___x_2091_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__1(v_a_2028_, v___x_2090_);
v___x_2092_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v___x_2091_, v___x_2072_);
lean_dec(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_0interp(lean_interpreter_value* stack)
{
lean_object* v_cs_2027_ = stack[0].m_obj;
lean_object* v_a_2028_ = stack[1].m_obj;
lean_object* v_a_2029_ = stack[2].m_obj;
lean_object* v_a_2030_ = stack[3].m_obj;
lean_object* v_a_2031_ = stack[4].m_obj;
lean_object* v_a_2032_ = stack[5].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(lean_object* v_cs_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cs_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
return v_res_2106_;
}
}
lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* v_x_2107_, lean_object* v_x_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v_x_2107_, v_x_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2107_ = stack[0].m_obj;
lean_object* v_x_2108_ = stack[1].m_obj;
lean_object* v___y_2109_ = stack[2].m_obj;
lean_object* v___y_2110_ = stack[3].m_obj;
lean_object* v___y_2111_ = stack[4].m_obj;
lean_object* v___y_2112_ = stack[5].m_obj;
lean_object* v___y_2113_ = stack[6].m_obj;
lean_object* v_res_2116_;
v_res_2116_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2107_, v_x_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
stack->m_obj
 = v_res_2116_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* v_x_2117_, lean_object* v_x_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(v_x_2117_, v_x_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(lean_object* v_as_2126_, lean_object* v_as_x27_2127_, lean_object* v_b_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___redArg(v_as_x27_2127_, v_b_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2___boxed(lean_object* v_as_2131_, lean_object* v_as_x27_2132_, lean_object* v_b_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__2_spec__2(v_as_2131_, v_as_x27_2132_, v_b_2133_, v_a_2134_);
lean_dec(v_as_x27_2132_);
lean_dec(v_as_2131_);
return v_res_2135_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(lean_object* v_a_2136_, lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 0)
{
uint8_t v___x_2138_; 
v___x_2138_ = 0;
return v___x_2138_;
}
else
{
lean_object* v_key_2139_; lean_object* v_tail_2140_; uint8_t v___x_2141_; 
v_key_2139_ = lean_ctor_get(v_x_2137_, 0);
v_tail_2140_ = lean_ctor_get(v_x_2137_, 2);
v___x_2141_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2139_, v_a_2136_);
if (v___x_2141_ == 0)
{
v_x_2137_ = v_tail_2140_;
goto _start;
}
else
{
return v___x_2141_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2136_ = stack[0].m_obj;
lean_object* v_x_2137_ = stack[1].m_obj;
uint8_t v_res_2143_;
v_res_2143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2136_, v_x_2137_);
stack->m_num = v_res_2143_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2144_, v_x_2145_);
lean_dec(v_x_2145_);
lean_dec(v_a_2144_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(lean_object* v_a_2148_, lean_object* v_b_2149_, lean_object* v_x_2150_){
_start:
{
if (lean_obj_tag(v_x_2150_) == 0)
{
lean_dec(v_b_2149_);
lean_dec(v_a_2148_);
return v_x_2150_;
}
else
{
lean_object* v_key_2151_; lean_object* v_value_2152_; lean_object* v_tail_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2165_; 
v_key_2151_ = lean_ctor_get(v_x_2150_, 0);
v_value_2152_ = lean_ctor_get(v_x_2150_, 1);
v_tail_2153_ = lean_ctor_get(v_x_2150_, 2);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2150_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2155_ = v_x_2150_;
v_isShared_2156_ = v_isSharedCheck_2165_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_tail_2153_);
lean_inc(v_value_2152_);
lean_inc(v_key_2151_);
lean_dec(v_x_2150_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2165_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_2151_, v_a_2148_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2148_, v_b_2149_, v_tail_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 2, v___x_2158_);
v___x_2160_ = v___x_2155_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_key_2151_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_value_2152_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v___x_2163_; 
lean_dec(v_value_2152_);
lean_dec(v_key_2151_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_b_2149_);
lean_ctor_set(v___x_2155_, 0, v_a_2148_);
v___x_2163_ = v___x_2155_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2148_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_b_2149_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_tail_2153_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
if (lean_obj_tag(v_x_2167_) == 0)
{
return v_x_2166_;
}
else
{
lean_object* v_key_2168_; lean_object* v_value_2169_; lean_object* v_tail_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2193_; 
v_key_2168_ = lean_ctor_get(v_x_2167_, 0);
v_value_2169_ = lean_ctor_get(v_x_2167_, 1);
v_tail_2170_ = lean_ctor_get(v_x_2167_, 2);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_x_2167_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2172_ = v_x_2167_;
v_isShared_2173_ = v_isSharedCheck_2193_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_tail_2170_);
lean_inc(v_value_2169_);
lean_inc(v_key_2168_);
lean_dec(v_x_2167_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2193_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; uint64_t v___x_2177_; uint64_t v_fold_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2174_ = lean_array_get_size(v_x_2166_);
v___x_2175_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_2168_);
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
v___x_2187_ = lean_array_uget_borrowed(v_x_2166_, v___x_2186_);
lean_inc(v___x_2187_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 2, v___x_2187_);
v___x_2189_ = v___x_2172_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_key_2168_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_value_2169_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_array_uset(v_x_2166_, v___x_2186_, v___x_2189_);
v_x_2166_ = v___x_2190_;
v_x_2167_ = v_tail_2170_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2194_, lean_object* v_source_2195_, lean_object* v_target_2196_){
_start:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_array_get_size(v_source_2195_);
v___x_2198_ = lean_nat_dec_lt(v_i_2194_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_dec_ref(v_source_2195_);
lean_dec(v_i_2194_);
return v_target_2196_;
}
else
{
lean_object* v_es_2199_; lean_object* v___x_2200_; lean_object* v_source_2201_; lean_object* v_target_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_es_2199_ = lean_array_fget(v_source_2195_, v_i_2194_);
v___x_2200_ = lean_box(0);
v_source_2201_ = lean_array_fset(v_source_2195_, v_i_2194_, v___x_2200_);
v_target_2202_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2196_, v_es_2199_);
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_nat_add(v_i_2194_, v___x_2203_);
lean_dec(v_i_2194_);
v_i_2194_ = v___x_2204_;
v_source_2195_ = v_source_2201_;
v_target_2196_ = v_target_2202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(lean_object* v_data_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_nbuckets_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2207_ = lean_array_get_size(v_data_2206_);
v___x_2208_ = lean_unsigned_to_nat(2u);
v_nbuckets_2209_ = lean_nat_mul(v___x_2207_, v___x_2208_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_mk_array(v_nbuckets_2209_, v___x_2211_);
v___x_2213_ = lean_array_propagate_mark(v_data_2206_, v___x_2212_);
v___x_2214_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_2210_, v_data_2206_, v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* v_m_2215_, lean_object* v_a_2216_, lean_object* v_b_2217_){
_start:
{
lean_object* v_size_2218_; lean_object* v_buckets_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2262_; 
v_size_2218_ = lean_ctor_get(v_m_2215_, 0);
v_buckets_2219_ = lean_ctor_get(v_m_2215_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_m_2215_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2221_ = v_m_2215_;
v_isShared_2222_ = v_isSharedCheck_2262_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_buckets_2219_);
lean_inc(v_size_2218_);
lean_dec(v_m_2215_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2262_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; uint64_t v___x_2224_; uint64_t v___x_2225_; uint64_t v___x_2226_; uint64_t v_fold_2227_; uint64_t v___x_2228_; uint64_t v___x_2229_; uint64_t v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; lean_object* v_bkt_2236_; uint8_t v___x_2237_; 
v___x_2223_ = lean_array_get_size(v_buckets_2219_);
v___x_2224_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_2216_);
v___x_2225_ = 32ULL;
v___x_2226_ = lean_uint64_shift_right(v___x_2224_, v___x_2225_);
v_fold_2227_ = lean_uint64_xor(v___x_2224_, v___x_2226_);
v___x_2228_ = 16ULL;
v___x_2229_ = lean_uint64_shift_right(v_fold_2227_, v___x_2228_);
v___x_2230_ = lean_uint64_xor(v_fold_2227_, v___x_2229_);
v___x_2231_ = lean_uint64_to_usize(v___x_2230_);
v___x_2232_ = lean_usize_of_nat(v___x_2223_);
v___x_2233_ = ((size_t)1ULL);
v___x_2234_ = lean_usize_sub(v___x_2232_, v___x_2233_);
v___x_2235_ = lean_usize_land(v___x_2231_, v___x_2234_);
v_bkt_2236_ = lean_array_uget_borrowed(v_buckets_2219_, v___x_2235_);
v___x_2237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2216_, v_bkt_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v_size_x27_2239_; lean_object* v___x_2240_; lean_object* v_buckets_x27_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v_size_x27_2239_ = lean_nat_add(v_size_2218_, v___x_2238_);
lean_dec(v_size_2218_);
lean_inc(v_bkt_2236_);
v___x_2240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2216_);
lean_ctor_set(v___x_2240_, 1, v_b_2217_);
lean_ctor_set(v___x_2240_, 2, v_bkt_2236_);
v_buckets_x27_2241_ = lean_array_uset(v_buckets_2219_, v___x_2235_, v___x_2240_);
v___x_2242_ = lean_unsigned_to_nat(4u);
v___x_2243_ = lean_nat_mul(v_size_x27_2239_, v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(3u);
v___x_2245_ = lean_nat_div(v___x_2243_, v___x_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_array_get_size(v_buckets_x27_2241_);
v___x_2247_ = lean_nat_dec_le(v___x_2245_, v___x_2246_);
lean_dec(v___x_2245_);
if (v___x_2247_ == 0)
{
lean_object* v_val_2248_; lean_object* v___x_2250_; 
v_val_2248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_2241_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_val_2248_);
lean_ctor_set(v___x_2221_, 0, v_size_x27_2239_);
v___x_2250_ = v___x_2221_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_size_x27_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_val_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v___x_2253_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_buckets_x27_2241_);
lean_ctor_set(v___x_2221_, 0, v_size_x27_2239_);
v___x_2253_ = v___x_2221_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_size_x27_2239_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_buckets_x27_2241_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v_buckets_x27_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
lean_inc(v_bkt_2236_);
v___x_2255_ = lean_box(0);
v_buckets_x27_2256_ = lean_array_uset(v_buckets_2219_, v___x_2235_, v___x_2255_);
v___x_2257_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2216_, v_b_2217_, v_bkt_2236_);
v___x_2258_ = lean_array_uset(v_buckets_x27_2256_, v___x_2235_, v___x_2257_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v___x_2258_);
v___x_2260_ = v___x_2221_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_size_2218_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* v_as_2263_, size_t v_i_2264_, size_t v_stop_2265_, lean_object* v_b_2266_){
_start:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_eq(v_i_2264_, v_stop_2265_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = ((size_t)1ULL);
v___x_2270_ = lean_usize_sub(v_i_2264_, v___x_2269_);
v___x_2271_ = lean_array_uget_borrowed(v_as_2263_, v___x_2270_);
v___x_2272_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_2271_);
v___x_2273_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_2266_, v___x_2272_, v___x_2268_);
v_i_2264_ = v___x_2270_;
v_b_2266_ = v___x_2273_;
goto _start;
}
else
{
return v_b_2266_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2263_ = stack[0].m_obj;
size_t v_i_2264_ = stack[1].m_num;
size_t v_stop_2265_ = stack[2].m_num;
lean_object* v_b_2266_ = stack[3].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2263_, v_i_2264_, v_stop_2265_, v_b_2266_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(lean_object* v_as_2276_, lean_object* v_i_2277_, lean_object* v_stop_2278_, lean_object* v_b_2279_){
_start:
{
size_t v_i_boxed_2280_; size_t v_stop_boxed_2281_; lean_object* v_res_2282_; 
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_stop_boxed_2281_ = lean_unbox_usize(v_stop_2278_);
lean_dec(v_stop_2278_);
v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_2276_, v_i_boxed_2280_, v_stop_boxed_2281_, v_b_2279_);
lean_dec_ref(v_as_2276_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* v_cs_2283_){
_start:
{
lean_object* v_alts_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_map_2299_; uint8_t v___x_2300_; 
v_alts_2284_ = lean_ctor_get(v_cs_2283_, 3);
v___x_2285_ = lean_array_get_size(v_alts_2284_);
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_nat_add(v___x_2285_, v___x_2286_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_unsigned_to_nat(4u);
v___x_2290_ = lean_nat_mul(v___x_2287_, v___x_2289_);
lean_dec(v___x_2287_);
v___x_2291_ = lean_unsigned_to_nat(3u);
v___x_2292_ = lean_nat_div(v___x_2290_, v___x_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = l_Nat_nextPowerOfTwo(v___x_2292_);
lean_dec(v___x_2292_);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_mk_array(v___x_2293_, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2288_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_box(2);
v___x_2298_ = lean_box(0);
v_map_2299_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_2296_, v___x_2297_, v___x_2298_);
v___x_2300_ = lean_nat_dec_lt(v___x_2288_, v___x_2285_);
if (v___x_2300_ == 0)
{
return v_map_2299_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = lean_usize_of_nat(v___x_2285_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_2284_, v___x_2301_, v___x_2302_, v_map_2299_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* v_cs_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_2304_);
lean_dec_ref(v_cs_2304_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* v_00_u03b2_2306_, lean_object* v_m_2307_, lean_object* v_a_2308_, lean_object* v_b_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_2307_, v_a_2308_, v_b_2309_);
return v___x_2310_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_object* v_00_u03b2_2311_, lean_object* v_a_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_2312_, v_x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2312_ = stack[1].m_obj;
lean_object* v_x_2313_ = stack[2].m_obj;
uint8_t v_res_2315_;
v_res_2315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(lean_box(0), v_a_2312_, v_x_2313_);
stack->m_num = v_res_2315_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2316_, lean_object* v_a_2317_, lean_object* v_x_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_2316_, v_a_2317_, v_x_2318_);
lean_dec(v_x_2318_);
lean_dec(v_a_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(lean_object* v_00_u03b2_2321_, lean_object* v_data_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(lean_object* v_00_u03b2_2324_, lean_object* v_a_2325_, lean_object* v_b_2326_, lean_object* v_x_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_2325_, v_b_2326_, v_x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2329_, lean_object* v_i_2330_, lean_object* v_source_2331_, lean_object* v_target_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_2330_, v_source_2331_, v_target_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2335_, v_x_2336_);
return v___x_2337_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* v_fvar_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2341_; lean_object* v_decision_2342_; uint8_t v___x_2343_; 
v___x_2341_ = lean_st_ref_get(v_a_2339_);
v_decision_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_ref(v_decision_2342_);
lean_dec(v___x_2341_);
v___x_2343_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_2342_, v_fvar_2338_);
lean_dec_ref(v_decision_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_fvar_2338_);
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v_decision_2347_; lean_object* v_newArms_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2360_; 
v___x_2346_ = lean_st_ref_take(v_a_2339_);
v_decision_2347_ = lean_ctor_get(v___x_2346_, 0);
v_newArms_2348_ = lean_ctor_get(v___x_2346_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2350_ = v___x_2346_;
v_isShared_2351_ = v_isSharedCheck_2360_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_newArms_2348_);
lean_inc(v_decision_2347_);
lean_dec(v___x_2346_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2360_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_box(2);
v___x_2354_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_2347_, v_fvar_2338_, v___x_2353_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2354_);
v___x_2356_ = v___x_2350_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_newArms_2348_);
v___x_2356_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_st_ref_put(v_a_2339_, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2352_);
return v___x_2358_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_2338_ = stack[0].m_obj;
lean_object* v_a_2339_ = stack[1].m_obj;
lean_object* v_res_2361_;
v_res_2361_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2338_, v_a_2339_);
stack->m_obj
 = v_res_2361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* v_fvar_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2362_, v_a_2363_);
lean_dec(v_a_2363_);
return v_res_2365_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* v_fvar_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_2366_, v_a_2367_);
return v___x_2374_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_2366_ = stack[0].m_obj;
lean_object* v_a_2367_ = stack[1].m_obj;
lean_object* v_a_2368_ = stack[2].m_obj;
lean_object* v_a_2369_ = stack[3].m_obj;
lean_object* v_a_2370_ = stack[4].m_obj;
lean_object* v_a_2371_ = stack[5].m_obj;
lean_object* v_a_2372_ = stack[6].m_obj;
lean_object* v_res_2375_;
v_res_2375_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
stack->m_obj
 = v_res_2375_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* v_fvar_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(v_fvar_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec(v_a_2377_);
return v_res_2384_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_toApplicative_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2458_; 
v___x_2393_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
v___x_2394_ = l_StateRefT_x27_instMonad___redArg(v___x_2393_);
v_toApplicative_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2394_, 1);
lean_dec(v_unused_2459_);
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2458_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_toApplicative_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2458_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_toFunctor_2399_; lean_object* v_toSeq_2400_; lean_object* v_toSeqLeft_2401_; lean_object* v_toSeqRight_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2456_; 
v_toFunctor_2399_ = lean_ctor_get(v_toApplicative_2395_, 0);
v_toSeq_2400_ = lean_ctor_get(v_toApplicative_2395_, 2);
v_toSeqLeft_2401_ = lean_ctor_get(v_toApplicative_2395_, 3);
v_toSeqRight_2402_ = lean_ctor_get(v_toApplicative_2395_, 4);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_toApplicative_2395_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v_toApplicative_2395_, 1);
lean_dec(v_unused_2457_);
v___x_2404_ = v_toApplicative_2395_;
v_isShared_2405_ = v_isSharedCheck_2456_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_toSeqRight_2402_);
lean_inc(v_toSeqLeft_2401_);
lean_inc(v_toSeq_2400_);
lean_inc(v_toFunctor_2399_);
lean_dec(v_toApplicative_2395_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2456_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___f_2408_; lean_object* v___f_2409_; lean_object* v___x_2410_; lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___x_2415_; 
v___f_2406_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1));
v___f_2407_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2399_);
v___f_2408_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2408_, 0, v_toFunctor_2399_);
v___f_2409_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2409_, 0, v_toFunctor_2399_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___f_2408_);
lean_ctor_set(v___x_2410_, 1, v___f_2409_);
v___f_2411_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2411_, 0, v_toSeqRight_2402_);
v___f_2412_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2412_, 0, v_toSeqLeft_2401_);
v___f_2413_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2413_, 0, v_toSeq_2400_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v___f_2411_);
lean_ctor_set(v___x_2404_, 3, v___f_2412_);
lean_ctor_set(v___x_2404_, 2, v___f_2413_);
lean_ctor_set(v___x_2404_, 1, v___f_2406_);
lean_ctor_set(v___x_2404_, 0, v___x_2410_);
v___x_2415_ = v___x_2404_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___f_2406_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___f_2413_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v___f_2412_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v___f_2411_);
v___x_2415_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v___f_2407_);
lean_ctor_set(v___x_2397_, 0, v___x_2415_);
v___x_2417_ = v___x_2397_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v___f_2407_);
v___x_2417_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v_toApplicative_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2452_; 
v___x_2418_ = l_StateRefT_x27_instMonad___redArg(v___x_2417_);
v_toApplicative_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2418_, 1);
lean_dec(v_unused_2453_);
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2452_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_toApplicative_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2452_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_toFunctor_2423_; lean_object* v_toSeq_2424_; lean_object* v_toSeqLeft_2425_; lean_object* v_toSeqRight_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2450_; 
v_toFunctor_2423_ = lean_ctor_get(v_toApplicative_2419_, 0);
v_toSeq_2424_ = lean_ctor_get(v_toApplicative_2419_, 2);
v_toSeqLeft_2425_ = lean_ctor_get(v_toApplicative_2419_, 3);
v_toSeqRight_2426_ = lean_ctor_get(v_toApplicative_2419_, 4);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_toApplicative_2419_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v_toApplicative_2419_, 1);
lean_dec(v_unused_2451_);
v___x_2428_ = v_toApplicative_2419_;
v_isShared_2429_ = v_isSharedCheck_2450_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_toSeqRight_2426_);
lean_inc(v_toSeqLeft_2425_);
lean_inc(v_toSeq_2424_);
lean_inc(v_toFunctor_2423_);
lean_dec(v_toApplicative_2419_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2450_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___f_2430_; lean_object* v___f_2431_; lean_object* v___f_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___f_2436_; lean_object* v___f_2437_; lean_object* v___x_2439_; 
v___f_2430_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3));
v___f_2431_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2423_);
v___f_2432_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2432_, 0, v_toFunctor_2423_);
v___f_2433_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2433_, 0, v_toFunctor_2423_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___f_2432_);
lean_ctor_set(v___x_2434_, 1, v___f_2433_);
v___f_2435_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2435_, 0, v_toSeqRight_2426_);
v___f_2436_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2436_, 0, v_toSeqLeft_2425_);
v___f_2437_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2437_, 0, v_toSeq_2424_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 4, v___f_2435_);
lean_ctor_set(v___x_2428_, 3, v___f_2436_);
lean_ctor_set(v___x_2428_, 2, v___f_2437_);
lean_ctor_set(v___x_2428_, 1, v___f_2430_);
lean_ctor_set(v___x_2428_, 0, v___x_2434_);
v___x_2439_ = v___x_2428_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___f_2430_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v___f_2437_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v___f_2436_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v___f_2435_);
v___x_2439_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2441_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___f_2431_);
lean_ctor_set(v___x_2421_, 0, v___x_2439_);
v___x_2441_ = v___x_2421_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___f_2431_);
v___x_2441_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_10720__overap_2446_; lean_object* v___x_2447_; 
v___x_2442_ = l_ReaderT_instMonad___redArg(v___x_2441_);
v___x_2443_ = l_StateRefT_x27_instMonad___redArg(v___x_2442_);
v___x_2444_ = lean_box(0);
v___x_2445_ = l_instInhabitedOfMonad___redArg(v___x_2443_, v___x_2444_);
v___x_10720__overap_2446_ = lean_panic_fn_borrowed(v___x_2445_, v_msg_2385_);
lean_dec(v___x_2445_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
lean_inc(v___y_2387_);
lean_inc(v___y_2386_);
v___x_2447_ = lean_apply_7(v___x_10720__overap_2446_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, lean_box(0));
return v___x_2447_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2385_ = stack[0].m_obj;
lean_object* v___y_2386_ = stack[1].m_obj;
lean_object* v___y_2387_ = stack[2].m_obj;
lean_object* v___y_2388_ = stack[3].m_obj;
lean_object* v___y_2389_ = stack[4].m_obj;
lean_object* v___y_2390_ = stack[5].m_obj;
lean_object* v___y_2391_ = stack[6].m_obj;
lean_object* v_res_2460_;
v_res_2460_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
stack->m_obj
 = v_res_2460_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(lean_object* v_msg_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
return v_res_2469_;
}
}
lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(lean_object* v_f_2470_, lean_object* v_e_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_ty_2480_; lean_object* v_body_2481_; uint8_t v___x_2484_; 
v___x_2484_ = l_Lean_Expr_hasFVar(v_e_2471_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v_e_2471_);
lean_dec_ref(v_f_2470_);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
return v___x_2486_;
}
else
{
switch(lean_obj_tag(v_e_2471_))
{
case 1:
{
lean_object* v_fvarId_2487_; lean_object* v___x_2488_; 
v_fvarId_2487_ = lean_ctor_get(v_e_2471_, 0);
lean_inc(v_fvarId_2487_);
lean_dec_ref_known(v_e_2471_, 1);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc(v___y_2473_);
lean_inc(v___y_2472_);
v___x_2488_ = lean_apply_8(v_f_2470_, v_fvarId_2487_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, lean_box(0));
return v___x_2488_;
}
case 2:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_dec_ref_known(v_e_2471_, 1);
lean_dec_ref(v_f_2470_);
v___x_2489_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2490_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2489_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2490_;
}
case 5:
{
lean_object* v_fn_2491_; lean_object* v_arg_2492_; lean_object* v___x_2493_; 
v_fn_2491_ = lean_ctor_get(v_e_2471_, 0);
lean_inc_ref(v_fn_2491_);
v_arg_2492_ = lean_ctor_get(v_e_2471_, 1);
lean_inc_ref(v_arg_2492_);
lean_dec_ref_known(v_e_2471_, 2);
lean_inc_ref(v_f_2470_);
v___x_2493_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2470_, v_fn_2491_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_dec_ref_known(v___x_2493_, 1);
v_e_2471_ = v_arg_2492_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_f_2470_);
return v___x_2493_;
}
}
case 6:
{
lean_object* v_binderType_2495_; lean_object* v_body_2496_; 
v_binderType_2495_ = lean_ctor_get(v_e_2471_, 1);
lean_inc_ref(v_binderType_2495_);
v_body_2496_ = lean_ctor_get(v_e_2471_, 2);
lean_inc_ref(v_body_2496_);
lean_dec_ref_known(v_e_2471_, 3);
v_ty_2480_ = v_binderType_2495_;
v_body_2481_ = v_body_2496_;
goto v___jp_2479_;
}
case 7:
{
lean_object* v_binderType_2497_; lean_object* v_body_2498_; 
v_binderType_2497_ = lean_ctor_get(v_e_2471_, 1);
lean_inc_ref(v_binderType_2497_);
v_body_2498_ = lean_ctor_get(v_e_2471_, 2);
lean_inc_ref(v_body_2498_);
lean_dec_ref_known(v_e_2471_, 3);
v_ty_2480_ = v_binderType_2497_;
v_body_2481_ = v_body_2498_;
goto v___jp_2479_;
}
case 8:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref_known(v_e_2471_, 4);
lean_dec_ref(v_f_2470_);
v___x_2499_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2500_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2499_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2500_;
}
case 11:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec_ref_known(v_e_2471_, 3);
lean_dec_ref(v_f_2470_);
v___x_2501_ = lean_obj_once(&l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3, &l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once, _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
v___x_2502_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_2501_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2502_;
}
default: 
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v_e_2471_);
lean_dec_ref(v_f_2470_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
}
v___jp_2479_:
{
lean_object* v___x_2482_; 
lean_inc_ref(v_f_2470_);
v___x_2482_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2470_, v_ty_2480_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_dec_ref_known(v___x_2482_, 1);
v_e_2471_ = v_body_2481_;
goto _start;
}
else
{
lean_dec_ref(v_body_2481_);
lean_dec_ref(v_f_2470_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2470_ = stack[0].m_obj;
lean_object* v_e_2471_ = stack[1].m_obj;
lean_object* v___y_2472_ = stack[2].m_obj;
lean_object* v___y_2473_ = stack[3].m_obj;
lean_object* v___y_2474_ = stack[4].m_obj;
lean_object* v___y_2475_ = stack[5].m_obj;
lean_object* v___y_2476_ = stack[6].m_obj;
lean_object* v___y_2477_ = stack[7].m_obj;
lean_object* v_res_2505_;
v_res_2505_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2470_, v_e_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2505_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(lean_object* v_f_2506_, lean_object* v_e_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2506_, v_e_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec(v___y_2508_);
return v_res_2515_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(lean_object* v_f_2516_, lean_object* v_arg_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
switch(lean_obj_tag(v_arg_2517_))
{
case 0:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_f_2516_);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
case 1:
{
lean_object* v_fvarId_2527_; lean_object* v___x_2528_; 
v_fvarId_2527_ = lean_ctor_get(v_arg_2517_, 0);
lean_inc(v_fvarId_2527_);
lean_dec_ref_known(v_arg_2517_, 1);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc(v___y_2518_);
v___x_2528_ = lean_apply_8(v_f_2516_, v_fvarId_2527_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, lean_box(0));
return v___x_2528_;
}
default: 
{
lean_object* v_expr_2529_; lean_object* v___x_2530_; 
v_expr_2529_ = lean_ctor_get(v_arg_2517_, 0);
lean_inc_ref(v_expr_2529_);
lean_dec_ref_known(v_arg_2517_, 1);
v___x_2530_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2516_, v_expr_2529_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v___x_2530_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2516_ = stack[0].m_obj;
lean_object* v_arg_2517_ = stack[1].m_obj;
lean_object* v___y_2518_ = stack[2].m_obj;
lean_object* v___y_2519_ = stack[3].m_obj;
lean_object* v___y_2520_ = stack[4].m_obj;
lean_object* v___y_2521_ = stack[5].m_obj;
lean_object* v___y_2522_ = stack[6].m_obj;
lean_object* v___y_2523_ = stack[7].m_obj;
lean_object* v_res_2531_;
v_res_2531_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2516_, v_arg_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
stack->m_obj
 = v_res_2531_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(lean_object* v_f_2532_, lean_object* v_arg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2532_, v_arg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec(v___y_2534_);
return v_res_2541_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(lean_object* v_f_2542_, lean_object* v_param_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_type_2551_; lean_object* v___x_2552_; 
v_type_2551_ = lean_ctor_get(v_param_2543_, 2);
lean_inc_ref(v_type_2551_);
lean_dec_ref(v_param_2543_);
v___x_2552_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2542_, v_type_2551_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
return v___x_2552_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2542_ = stack[0].m_obj;
lean_object* v_param_2543_ = stack[1].m_obj;
lean_object* v___y_2544_ = stack[2].m_obj;
lean_object* v___y_2545_ = stack[3].m_obj;
lean_object* v___y_2546_ = stack[4].m_obj;
lean_object* v___y_2547_ = stack[5].m_obj;
lean_object* v___y_2548_ = stack[6].m_obj;
lean_object* v___y_2549_ = stack[7].m_obj;
lean_object* v_res_2553_;
v_res_2553_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2542_, v_param_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
stack->m_obj
 = v_res_2553_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(lean_object* v_f_2554_, lean_object* v_param_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2554_, v_param_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec(v___y_2556_);
return v_res_2563_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(uint8_t v_pu_2564_, lean_object* v_f_2565_, lean_object* v_as_2566_, size_t v_i_2567_, size_t v_stop_2568_, lean_object* v_b_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_usize_dec_eq(v_i_2567_, v_stop_2568_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_array_uget_borrowed(v_as_2566_, v_i_2567_);
lean_inc(v___x_2578_);
lean_inc_ref(v_f_2565_);
v___x_2579_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_2565_, v___x_2578_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; size_t v___x_2581_; size_t v___x_2582_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = ((size_t)1ULL);
v___x_2582_ = lean_usize_add(v_i_2567_, v___x_2581_);
v_i_2567_ = v___x_2582_;
v_b_2569_ = v_a_2580_;
goto _start;
}
else
{
lean_dec_ref(v_f_2565_);
return v___x_2579_;
}
}
else
{
lean_object* v___x_2584_; 
lean_dec_ref(v_f_2565_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_b_2569_);
return v___x_2584_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2564_ = stack[0].m_num;
lean_object* v_f_2565_ = stack[1].m_obj;
lean_object* v_as_2566_ = stack[2].m_obj;
size_t v_i_2567_ = stack[3].m_num;
size_t v_stop_2568_ = stack[4].m_num;
lean_object* v_b_2569_ = stack[5].m_obj;
lean_object* v___y_2570_ = stack[6].m_obj;
lean_object* v___y_2571_ = stack[7].m_obj;
lean_object* v___y_2572_ = stack[8].m_obj;
lean_object* v___y_2573_ = stack[9].m_obj;
lean_object* v___y_2574_ = stack[10].m_obj;
lean_object* v___y_2575_ = stack[11].m_obj;
lean_object* v_res_2585_;
v_res_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2564_, v_f_2565_, v_as_2566_, v_i_2567_, v_stop_2568_, v_b_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
stack->m_obj
 = v_res_2585_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(lean_object* v_pu_2586_, lean_object* v_f_2587_, lean_object* v_as_2588_, lean_object* v_i_2589_, lean_object* v_stop_2590_, lean_object* v_b_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v_pu_boxed_2599_; size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; lean_object* v_res_2602_; 
v_pu_boxed_2599_ = lean_unbox(v_pu_2586_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2589_);
lean_dec(v_i_2589_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2590_);
lean_dec(v_stop_2590_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_2599_, v_f_2587_, v_as_2588_, v_i_boxed_2600_, v_stop_boxed_2601_, v_b_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v_as_2588_);
return v_res_2602_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(uint8_t v_pu_2603_, lean_object* v_f_2604_, lean_object* v_as_2605_, size_t v_i_2606_, size_t v_stop_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_usize_dec_eq(v_i_2606_, v_stop_2607_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_array_uget_borrowed(v_as_2605_, v_i_2606_);
lean_inc(v___x_2617_);
lean_inc_ref(v_f_2604_);
v___x_2618_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2604_, v___x_2617_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; size_t v___x_2620_; size_t v___x_2621_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = ((size_t)1ULL);
v___x_2621_ = lean_usize_add(v_i_2606_, v___x_2620_);
v_i_2606_ = v___x_2621_;
v_b_2608_ = v_a_2619_;
goto _start;
}
else
{
lean_dec_ref(v_f_2604_);
return v___x_2618_;
}
}
else
{
lean_object* v___x_2623_; 
lean_dec_ref(v_f_2604_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_b_2608_);
return v___x_2623_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2603_ = stack[0].m_num;
lean_object* v_f_2604_ = stack[1].m_obj;
lean_object* v_as_2605_ = stack[2].m_obj;
size_t v_i_2606_ = stack[3].m_num;
size_t v_stop_2607_ = stack[4].m_num;
lean_object* v_b_2608_ = stack[5].m_obj;
lean_object* v___y_2609_ = stack[6].m_obj;
lean_object* v___y_2610_ = stack[7].m_obj;
lean_object* v___y_2611_ = stack[8].m_obj;
lean_object* v___y_2612_ = stack[9].m_obj;
lean_object* v___y_2613_ = stack[10].m_obj;
lean_object* v___y_2614_ = stack[11].m_obj;
lean_object* v_res_2624_;
v_res_2624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2603_, v_f_2604_, v_as_2605_, v_i_2606_, v_stop_2607_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
stack->m_obj
 = v_res_2624_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(lean_object* v_pu_2625_, lean_object* v_f_2626_, lean_object* v_as_2627_, lean_object* v_i_2628_, lean_object* v_stop_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v_pu_boxed_2638_; size_t v_i_boxed_2639_; size_t v_stop_boxed_2640_; lean_object* v_res_2641_; 
v_pu_boxed_2638_ = lean_unbox(v_pu_2625_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_stop_boxed_2640_ = lean_unbox_usize(v_stop_2629_);
lean_dec(v_stop_2629_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_2638_, v_f_2626_, v_as_2627_, v_i_boxed_2639_, v_stop_boxed_2640_, v_b_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v_as_2627_);
return v_res_2641_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(uint8_t v_pu_2642_, lean_object* v_f_2643_, lean_object* v_e_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_args_2653_; 
switch(lean_obj_tag(v_e_2644_))
{
case 2:
{
lean_object* v_struct_2662_; lean_object* v___x_2663_; 
v_struct_2662_ = lean_ctor_get(v_e_2644_, 2);
lean_inc(v_struct_2662_);
lean_dec_ref_known(v_e_2644_, 3);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2663_ = lean_apply_8(v_f_2643_, v_struct_2662_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2663_;
}
case 3:
{
lean_object* v_args_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_args_2664_ = lean_ctor_get(v_e_2644_, 2);
lean_inc_ref(v_args_2664_);
lean_dec_ref_known(v_e_2644_, 3);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v_args_2664_);
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref(v_args_2664_);
lean_dec_ref(v_f_2643_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
return v___x_2669_;
}
else
{
size_t v___x_2670_; size_t v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = lean_usize_of_nat(v___x_2666_);
v___x_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2642_, v_f_2643_, v_args_2664_, v___x_2670_, v___x_2671_, v___x_2667_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec_ref(v_args_2664_);
return v___x_2672_;
}
}
case 4:
{
lean_object* v_fvarId_2673_; lean_object* v_args_2674_; lean_object* v___x_2675_; 
v_fvarId_2673_ = lean_ctor_get(v_e_2644_, 0);
lean_inc(v_fvarId_2673_);
v_args_2674_ = lean_ctor_get(v_e_2644_, 1);
lean_inc_ref(v_args_2674_);
lean_dec_ref_known(v_e_2644_, 2);
lean_inc_ref(v_f_2643_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2675_ = lean_apply_8(v_f_2643_, v_fvarId_2673_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2689_; 
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v___x_2675_, 0);
lean_dec(v_unused_2690_);
v___x_2677_ = v___x_2675_;
v_isShared_2678_ = v_isSharedCheck_2689_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v___x_2675_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2689_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2679_ = lean_unsigned_to_nat(0u);
v___x_2680_ = lean_array_get_size(v_args_2674_);
v___x_2681_ = lean_box(0);
v___x_2682_ = lean_nat_dec_lt(v___x_2679_, v___x_2680_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v_args_2674_);
lean_dec_ref(v_f_2643_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2681_);
v___x_2684_ = v___x_2677_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2681_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
size_t v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; 
lean_del_object(v___x_2677_);
v___x_2686_ = ((size_t)0ULL);
v___x_2687_ = lean_usize_of_nat(v___x_2680_);
v___x_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2642_, v_f_2643_, v_args_2674_, v___x_2686_, v___x_2687_, v___x_2681_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec_ref(v_args_2674_);
return v___x_2688_;
}
}
}
else
{
lean_dec_ref(v_args_2674_);
lean_dec_ref(v_f_2643_);
return v___x_2675_;
}
}
case 5:
{
lean_object* v_args_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_args_2691_ = lean_ctor_get(v_e_2644_, 1);
lean_inc_ref(v_args_2691_);
lean_dec_ref_known(v_e_2644_, 2);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_array_get_size(v_args_2691_);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
lean_dec_ref(v_args_2691_);
lean_dec_ref(v_f_2643_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
return v___x_2696_;
}
else
{
size_t v___x_2697_; size_t v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = ((size_t)0ULL);
v___x_2698_ = lean_usize_of_nat(v___x_2693_);
v___x_2699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2642_, v_f_2643_, v_args_2691_, v___x_2697_, v___x_2698_, v___x_2694_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec_ref(v_args_2691_);
return v___x_2699_;
}
}
case 6:
{
lean_object* v_var_2700_; lean_object* v___x_2701_; 
v_var_2700_ = lean_ctor_get(v_e_2644_, 1);
lean_inc(v_var_2700_);
lean_dec_ref_known(v_e_2644_, 2);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2701_ = lean_apply_8(v_f_2643_, v_var_2700_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2701_;
}
case 7:
{
lean_object* v_var_2702_; lean_object* v___x_2703_; 
v_var_2702_ = lean_ctor_get(v_e_2644_, 1);
lean_inc(v_var_2702_);
lean_dec_ref_known(v_e_2644_, 2);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2703_ = lean_apply_8(v_f_2643_, v_var_2702_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2703_;
}
case 8:
{
lean_object* v_var_2704_; lean_object* v___x_2705_; 
v_var_2704_ = lean_ctor_get(v_e_2644_, 2);
lean_inc(v_var_2704_);
lean_dec_ref_known(v_e_2644_, 3);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2705_ = lean_apply_8(v_f_2643_, v_var_2704_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2705_;
}
case 9:
{
lean_object* v_args_2706_; 
v_args_2706_ = lean_ctor_get(v_e_2644_, 1);
lean_inc_ref(v_args_2706_);
lean_dec_ref_known(v_e_2644_, 2);
v_args_2653_ = v_args_2706_;
goto v___jp_2652_;
}
case 10:
{
lean_object* v_args_2707_; 
v_args_2707_ = lean_ctor_get(v_e_2644_, 1);
lean_inc_ref(v_args_2707_);
lean_dec_ref_known(v_e_2644_, 2);
v_args_2653_ = v_args_2707_;
goto v___jp_2652_;
}
case 11:
{
lean_object* v_var_2708_; lean_object* v___x_2709_; 
v_var_2708_ = lean_ctor_get(v_e_2644_, 1);
lean_inc(v_var_2708_);
lean_dec_ref_known(v_e_2644_, 2);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2709_ = lean_apply_8(v_f_2643_, v_var_2708_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2709_;
}
case 12:
{
lean_object* v_var_2710_; lean_object* v_args_2711_; lean_object* v___x_2712_; 
v_var_2710_ = lean_ctor_get(v_e_2644_, 0);
lean_inc(v_var_2710_);
v_args_2711_ = lean_ctor_get(v_e_2644_, 2);
lean_inc_ref(v_args_2711_);
lean_dec_ref_known(v_e_2644_, 3);
lean_inc_ref(v_f_2643_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2712_ = lean_apply_8(v_f_2643_, v_var_2710_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2726_; 
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; 
v_unused_2727_ = lean_ctor_get(v___x_2712_, 0);
lean_dec(v_unused_2727_);
v___x_2714_ = v___x_2712_;
v_isShared_2715_ = v_isSharedCheck_2726_;
goto v_resetjp_2713_;
}
else
{
lean_dec(v___x_2712_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2726_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_array_get_size(v_args_2711_);
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_nat_dec_lt(v___x_2716_, v___x_2717_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2721_; 
lean_dec_ref(v_args_2711_);
lean_dec_ref(v_f_2643_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2718_);
v___x_2721_ = v___x_2714_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2718_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
size_t v___x_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2714_);
v___x_2723_ = ((size_t)0ULL);
v___x_2724_ = lean_usize_of_nat(v___x_2717_);
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2642_, v_f_2643_, v_args_2711_, v___x_2723_, v___x_2724_, v___x_2718_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec_ref(v_args_2711_);
return v___x_2725_;
}
}
}
else
{
lean_dec_ref(v_args_2711_);
lean_dec_ref(v_f_2643_);
return v___x_2712_;
}
}
case 13:
{
lean_object* v_fvarId_2728_; lean_object* v___x_2729_; 
v_fvarId_2728_ = lean_ctor_get(v_e_2644_, 1);
lean_inc(v_fvarId_2728_);
lean_dec_ref_known(v_e_2644_, 2);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2729_ = lean_apply_8(v_f_2643_, v_fvarId_2728_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2729_;
}
case 14:
{
lean_object* v_fvarId_2730_; lean_object* v___x_2731_; 
v_fvarId_2730_ = lean_ctor_get(v_e_2644_, 0);
lean_inc(v_fvarId_2730_);
lean_dec_ref_known(v_e_2644_, 1);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2731_ = lean_apply_8(v_f_2643_, v_fvarId_2730_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2731_;
}
case 15:
{
lean_object* v_fvarId_2732_; lean_object* v___x_2733_; 
v_fvarId_2732_ = lean_ctor_get(v_e_2644_, 0);
lean_inc(v_fvarId_2732_);
lean_dec_ref_known(v_e_2644_, 1);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2733_ = lean_apply_8(v_f_2643_, v_fvarId_2732_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2733_;
}
default: 
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_dec(v_e_2644_);
lean_dec_ref(v_f_2643_);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_get_size(v_args_2653_);
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_nat_dec_lt(v___x_2654_, v___x_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec_ref(v_args_2653_);
lean_dec_ref(v_f_2643_);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
return v___x_2658_;
}
else
{
size_t v___x_2659_; size_t v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = lean_usize_of_nat(v___x_2655_);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2642_, v_f_2643_, v_args_2653_, v___x_2659_, v___x_2660_, v___x_2656_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec_ref(v_args_2653_);
return v___x_2661_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2642_ = stack[0].m_num;
lean_object* v_f_2643_ = stack[1].m_obj;
lean_object* v_e_2644_ = stack[2].m_obj;
lean_object* v___y_2645_ = stack[3].m_obj;
lean_object* v___y_2646_ = stack[4].m_obj;
lean_object* v___y_2647_ = stack[5].m_obj;
lean_object* v___y_2648_ = stack[6].m_obj;
lean_object* v___y_2649_ = stack[7].m_obj;
lean_object* v___y_2650_ = stack[8].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2642_, v_f_2643_, v_e_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(lean_object* v_pu_2737_, lean_object* v_f_2738_, lean_object* v_e_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v_pu_boxed_2747_; lean_object* v_res_2748_; 
v_pu_boxed_2747_ = lean_unbox(v_pu_2737_);
v_res_2748_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_2747_, v_f_2738_, v_e_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
return v_res_2748_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(uint8_t v_pu_2749_, lean_object* v_f_2750_, lean_object* v_decl_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_type_2759_; lean_object* v_value_2760_; lean_object* v___x_2761_; 
v_type_2759_ = lean_ctor_get(v_decl_2751_, 2);
lean_inc_ref(v_type_2759_);
v_value_2760_ = lean_ctor_get(v_decl_2751_, 3);
lean_inc(v_value_2760_);
lean_dec_ref(v_decl_2751_);
lean_inc_ref(v_f_2750_);
v___x_2761_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2750_, v_type_2759_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; 
lean_dec_ref_known(v___x_2761_, 1);
v___x_2762_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_2749_, v_f_2750_, v_value_2760_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
return v___x_2762_;
}
else
{
lean_dec(v_value_2760_);
lean_dec_ref(v_f_2750_);
return v___x_2761_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2749_ = stack[0].m_num;
lean_object* v_f_2750_ = stack[1].m_obj;
lean_object* v_decl_2751_ = stack[2].m_obj;
lean_object* v___y_2752_ = stack[3].m_obj;
lean_object* v___y_2753_ = stack[4].m_obj;
lean_object* v___y_2754_ = stack[5].m_obj;
lean_object* v___y_2755_ = stack[6].m_obj;
lean_object* v___y_2756_ = stack[7].m_obj;
lean_object* v___y_2757_ = stack[8].m_obj;
lean_object* v_res_2763_;
v_res_2763_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2749_, v_f_2750_, v_decl_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
stack->m_obj
 = v_res_2763_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(lean_object* v_pu_2764_, lean_object* v_f_2765_, lean_object* v_decl_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
uint8_t v_pu_boxed_2774_; lean_object* v_res_2775_; 
v_pu_boxed_2774_ = lean_unbox(v_pu_2764_);
v_res_2775_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_2774_, v_f_2765_, v_decl_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec(v___y_2767_);
return v_res_2775_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(lean_object* v_alt_2776_, lean_object* v_f_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
switch(lean_obj_tag(v_alt_2776_))
{
case 0:
{
lean_object* v_code_2785_; lean_object* v___x_2786_; 
v_code_2785_ = lean_ctor_get(v_alt_2776_, 2);
lean_inc_ref(v_code_2785_);
lean_dec_ref_known(v_alt_2776_, 3);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2786_ = lean_apply_8(v_f_2777_, v_code_2785_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
return v___x_2786_;
}
case 1:
{
lean_object* v_code_2787_; lean_object* v___x_2788_; 
v_code_2787_ = lean_ctor_get(v_alt_2776_, 1);
lean_inc_ref(v_code_2787_);
lean_dec_ref_known(v_alt_2776_, 2);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2788_ = lean_apply_8(v_f_2777_, v_code_2787_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
return v___x_2788_;
}
default: 
{
lean_object* v_code_2789_; lean_object* v___x_2790_; 
v_code_2789_ = lean_ctor_get(v_alt_2776_, 0);
lean_inc_ref(v_code_2789_);
lean_dec_ref_known(v_alt_2776_, 1);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
lean_inc(v___y_2779_);
lean_inc(v___y_2778_);
v___x_2790_ = lean_apply_8(v_f_2777_, v_code_2789_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, lean_box(0));
return v___x_2790_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_2776_ = stack[0].m_obj;
lean_object* v_f_2777_ = stack[1].m_obj;
lean_object* v___y_2778_ = stack[2].m_obj;
lean_object* v___y_2779_ = stack[3].m_obj;
lean_object* v___y_2780_ = stack[4].m_obj;
lean_object* v___y_2781_ = stack[5].m_obj;
lean_object* v___y_2782_ = stack[6].m_obj;
lean_object* v___y_2783_ = stack[7].m_obj;
lean_object* v_res_2791_;
v_res_2791_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2776_, v_f_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
stack->m_obj
 = v_res_2791_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_alt_2792_, lean_object* v_f_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_2792_, v_f_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(lean_object* v_pu_2802_, lean_object* v_f_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
uint8_t v_pu_boxed_2812_; lean_object* v_res_2813_; 
v_pu_boxed_2812_ = lean_unbox(v_pu_2802_);
v_res_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_2812_, v_f_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
return v_res_2813_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(uint8_t v_pu_2814_, lean_object* v_f_2815_, lean_object* v_as_2816_, size_t v_i_2817_, size_t v_stop_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = lean_usize_dec_eq(v_i_2817_, v_stop_2818_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___f_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2828_ = lean_box(v_pu_2814_);
lean_inc_ref(v_f_2815_);
v___f_2829_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2829_, 0, v___x_2828_);
lean_closure_set(v___f_2829_, 1, v_f_2815_);
v___x_2830_ = lean_array_uget_borrowed(v_as_2816_, v_i_2817_);
lean_inc(v___x_2830_);
v___x_2831_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_2830_, v___f_2829_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; size_t v___x_2833_; size_t v___x_2834_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_add(v_i_2817_, v___x_2833_);
v_i_2817_ = v___x_2834_;
v_b_2819_ = v_a_2832_;
goto _start;
}
else
{
lean_dec_ref(v_f_2815_);
return v___x_2831_;
}
}
else
{
lean_object* v___x_2836_; 
lean_dec_ref(v_f_2815_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_b_2819_);
return v___x_2836_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2814_ = stack[0].m_num;
lean_object* v_f_2815_ = stack[1].m_obj;
lean_object* v_as_2816_ = stack[2].m_obj;
size_t v_i_2817_ = stack[3].m_num;
size_t v_stop_2818_ = stack[4].m_num;
lean_object* v_b_2819_ = stack[5].m_obj;
lean_object* v___y_2820_ = stack[6].m_obj;
lean_object* v___y_2821_ = stack[7].m_obj;
lean_object* v___y_2822_ = stack[8].m_obj;
lean_object* v___y_2823_ = stack[9].m_obj;
lean_object* v___y_2824_ = stack[10].m_obj;
lean_object* v___y_2825_ = stack[11].m_obj;
lean_object* v_res_2837_;
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2814_, v_f_2815_, v_as_2816_, v_i_2817_, v_stop_2818_, v_b_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
stack->m_obj
 = v_res_2837_;
}
lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(uint8_t v_pu_2838_, lean_object* v_f_2839_, lean_object* v_c_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
switch(lean_obj_tag(v_c_2840_))
{
case 0:
{
lean_object* v_decl_2848_; lean_object* v_k_2849_; lean_object* v___x_2850_; 
v_decl_2848_ = lean_ctor_get(v_c_2840_, 0);
lean_inc_ref(v_decl_2848_);
v_k_2849_ = lean_ctor_get(v_c_2840_, 1);
lean_inc_ref(v_k_2849_);
lean_dec_ref_known(v_c_2840_, 2);
lean_inc_ref(v_f_2839_);
v___x_2850_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_2838_, v_f_2839_, v_decl_2848_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_dec_ref_known(v___x_2850_, 1);
v_c_2840_ = v_k_2849_;
goto _start;
}
else
{
lean_dec_ref(v_k_2849_);
lean_dec_ref(v_f_2839_);
return v___x_2850_;
}
}
case 3:
{
lean_object* v_fvarId_2852_; lean_object* v_args_2853_; lean_object* v___x_2854_; 
v_fvarId_2852_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2852_);
v_args_2853_ = lean_ctor_get(v_c_2840_, 1);
lean_inc_ref(v_args_2853_);
lean_dec_ref_known(v_c_2840_, 2);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2854_ = lean_apply_8(v_f_2839_, v_fvarId_2852_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2868_; 
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v___x_2854_, 0);
lean_dec(v_unused_2869_);
v___x_2856_ = v___x_2854_;
v_isShared_2857_ = v_isSharedCheck_2868_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v___x_2854_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2868_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_array_get_size(v_args_2853_);
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_nat_dec_lt(v___x_2858_, v___x_2859_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref(v_args_2853_);
lean_dec_ref(v_f_2839_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2860_);
v___x_2863_ = v___x_2856_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2860_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
else
{
size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
lean_del_object(v___x_2856_);
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = lean_usize_of_nat(v___x_2859_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_2838_, v_f_2839_, v_args_2853_, v___x_2865_, v___x_2866_, v___x_2860_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v_args_2853_);
return v___x_2867_;
}
}
}
else
{
lean_dec_ref(v_args_2853_);
lean_dec_ref(v_f_2839_);
return v___x_2854_;
}
}
case 4:
{
lean_object* v_cases_2870_; lean_object* v_resultType_2871_; lean_object* v_discr_2872_; lean_object* v_alts_2873_; lean_object* v___x_2874_; 
v_cases_2870_ = lean_ctor_get(v_c_2840_, 0);
lean_inc_ref(v_cases_2870_);
lean_dec_ref_known(v_c_2840_, 1);
v_resultType_2871_ = lean_ctor_get(v_cases_2870_, 1);
lean_inc_ref(v_resultType_2871_);
v_discr_2872_ = lean_ctor_get(v_cases_2870_, 2);
lean_inc(v_discr_2872_);
v_alts_2873_ = lean_ctor_get(v_cases_2870_, 3);
lean_inc_ref(v_alts_2873_);
lean_dec_ref(v_cases_2870_);
lean_inc_ref(v_f_2839_);
v___x_2874_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2839_, v_resultType_2871_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v___x_2875_; 
lean_dec_ref_known(v___x_2874_, 1);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2875_ = lean_apply_8(v_f_2839_, v_discr_2872_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2889_; 
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v___x_2875_, 0);
lean_dec(v_unused_2890_);
v___x_2877_ = v___x_2875_;
v_isShared_2878_ = v_isSharedCheck_2889_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v___x_2875_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2889_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = lean_array_get_size(v_alts_2873_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_nat_dec_lt(v___x_2879_, v___x_2880_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2884_; 
lean_dec_ref(v_alts_2873_);
lean_dec_ref(v_f_2839_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2881_);
v___x_2884_ = v___x_2877_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2881_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
else
{
size_t v___x_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
lean_del_object(v___x_2877_);
v___x_2886_ = ((size_t)0ULL);
v___x_2887_ = lean_usize_of_nat(v___x_2880_);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_2838_, v_f_2839_, v_alts_2873_, v___x_2886_, v___x_2887_, v___x_2881_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v_alts_2873_);
return v___x_2888_;
}
}
}
else
{
lean_dec_ref(v_alts_2873_);
lean_dec_ref(v_f_2839_);
return v___x_2875_;
}
}
else
{
lean_dec_ref(v_alts_2873_);
lean_dec(v_discr_2872_);
lean_dec_ref(v_f_2839_);
return v___x_2874_;
}
}
case 5:
{
lean_object* v_fvarId_2891_; lean_object* v___x_2892_; 
v_fvarId_2891_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2891_);
lean_dec_ref_known(v_c_2840_, 1);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2892_ = lean_apply_8(v_f_2839_, v_fvarId_2891_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
return v___x_2892_;
}
case 6:
{
lean_object* v_type_2893_; lean_object* v___x_2894_; 
v_type_2893_ = lean_ctor_get(v_c_2840_, 0);
lean_inc_ref(v_type_2893_);
lean_dec_ref_known(v_c_2840_, 1);
v___x_2894_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2839_, v_type_2893_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2894_;
}
case 7:
{
lean_object* v_fvarId_2895_; lean_object* v_y_2896_; lean_object* v_k_2897_; lean_object* v___x_2898_; 
v_fvarId_2895_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2895_);
v_y_2896_ = lean_ctor_get(v_c_2840_, 2);
lean_inc(v_y_2896_);
v_k_2897_ = lean_ctor_get(v_c_2840_, 3);
lean_inc_ref(v_k_2897_);
lean_dec_ref_known(v_c_2840_, 4);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2898_ = lean_apply_8(v_f_2839_, v_fvarId_2895_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref_known(v___x_2898_, 1);
lean_inc_ref(v_f_2839_);
v___x_2899_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_2839_, v_y_2896_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref_known(v___x_2899_, 1);
v_c_2840_ = v_k_2897_;
goto _start;
}
else
{
lean_dec_ref(v_k_2897_);
lean_dec_ref(v_f_2839_);
return v___x_2899_;
}
}
else
{
lean_dec_ref(v_k_2897_);
lean_dec(v_y_2896_);
lean_dec_ref(v_f_2839_);
return v___x_2898_;
}
}
case 8:
{
lean_object* v_fvarId_2901_; lean_object* v_y_2902_; lean_object* v_k_2903_; lean_object* v___x_2904_; 
v_fvarId_2901_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2901_);
v_y_2902_ = lean_ctor_get(v_c_2840_, 2);
lean_inc(v_y_2902_);
v_k_2903_ = lean_ctor_get(v_c_2840_, 3);
lean_inc_ref(v_k_2903_);
lean_dec_ref_known(v_c_2840_, 4);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2904_ = lean_apply_8(v_f_2839_, v_fvarId_2901_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; 
lean_dec_ref_known(v___x_2904_, 1);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2905_ = lean_apply_8(v_f_2839_, v_y_2902_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_dec_ref_known(v___x_2905_, 1);
v_c_2840_ = v_k_2903_;
goto _start;
}
else
{
lean_dec_ref(v_k_2903_);
lean_dec_ref(v_f_2839_);
return v___x_2905_;
}
}
else
{
lean_dec_ref(v_k_2903_);
lean_dec(v_y_2902_);
lean_dec_ref(v_f_2839_);
return v___x_2904_;
}
}
case 9:
{
lean_object* v_fvarId_2907_; lean_object* v_y_2908_; lean_object* v_ty_2909_; lean_object* v_k_2910_; lean_object* v___x_2911_; 
v_fvarId_2907_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2907_);
v_y_2908_ = lean_ctor_get(v_c_2840_, 3);
lean_inc(v_y_2908_);
v_ty_2909_ = lean_ctor_get(v_c_2840_, 4);
lean_inc_ref(v_ty_2909_);
v_k_2910_ = lean_ctor_get(v_c_2840_, 5);
lean_inc_ref(v_k_2910_);
lean_dec_ref_known(v_c_2840_, 6);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2911_ = lean_apply_8(v_f_2839_, v_fvarId_2907_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2912_; 
lean_dec_ref_known(v___x_2911_, 1);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2912_ = lean_apply_8(v_f_2839_, v_y_2908_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; 
lean_dec_ref_known(v___x_2912_, 1);
lean_inc_ref(v_f_2839_);
v___x_2913_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2839_, v_ty_2909_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref_known(v___x_2913_, 1);
v_c_2840_ = v_k_2910_;
goto _start;
}
else
{
lean_dec_ref(v_k_2910_);
lean_dec_ref(v_f_2839_);
return v___x_2913_;
}
}
else
{
lean_dec_ref(v_k_2910_);
lean_dec_ref(v_ty_2909_);
lean_dec_ref(v_f_2839_);
return v___x_2912_;
}
}
else
{
lean_dec_ref(v_k_2910_);
lean_dec_ref(v_ty_2909_);
lean_dec(v_y_2908_);
lean_dec_ref(v_f_2839_);
return v___x_2911_;
}
}
case 10:
{
lean_object* v_fvarId_2915_; lean_object* v_k_2916_; lean_object* v___x_2917_; 
v_fvarId_2915_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2915_);
v_k_2916_ = lean_ctor_get(v_c_2840_, 2);
lean_inc_ref(v_k_2916_);
lean_dec_ref_known(v_c_2840_, 3);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2917_ = lean_apply_8(v_f_2839_, v_fvarId_2915_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_dec_ref_known(v___x_2917_, 1);
v_c_2840_ = v_k_2916_;
goto _start;
}
else
{
lean_dec_ref(v_k_2916_);
lean_dec_ref(v_f_2839_);
return v___x_2917_;
}
}
case 11:
{
lean_object* v_fvarId_2919_; lean_object* v_k_2920_; lean_object* v___x_2921_; 
v_fvarId_2919_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2919_);
v_k_2920_ = lean_ctor_get(v_c_2840_, 2);
lean_inc_ref(v_k_2920_);
lean_dec_ref_known(v_c_2840_, 3);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2921_ = lean_apply_8(v_f_2839_, v_fvarId_2919_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_dec_ref_known(v___x_2921_, 1);
v_c_2840_ = v_k_2920_;
goto _start;
}
else
{
lean_dec_ref(v_k_2920_);
lean_dec_ref(v_f_2839_);
return v___x_2921_;
}
}
case 12:
{
lean_object* v_fvarId_2923_; lean_object* v_k_2924_; lean_object* v___x_2925_; 
v_fvarId_2923_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2923_);
v_k_2924_ = lean_ctor_get(v_c_2840_, 3);
lean_inc_ref(v_k_2924_);
lean_dec_ref_known(v_c_2840_, 4);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2925_ = lean_apply_8(v_f_2839_, v_fvarId_2923_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_dec_ref_known(v___x_2925_, 1);
v_c_2840_ = v_k_2924_;
goto _start;
}
else
{
lean_dec_ref(v_k_2924_);
lean_dec_ref(v_f_2839_);
return v___x_2925_;
}
}
case 13:
{
lean_object* v_fvarId_2927_; lean_object* v_k_2928_; lean_object* v___x_2929_; 
v_fvarId_2927_ = lean_ctor_get(v_c_2840_, 0);
lean_inc(v_fvarId_2927_);
v_k_2928_ = lean_ctor_get(v_c_2840_, 1);
lean_inc_ref(v_k_2928_);
lean_dec_ref_known(v_c_2840_, 2);
lean_inc_ref(v_f_2839_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc(v___y_2841_);
v___x_2929_ = lean_apply_8(v_f_2839_, v_fvarId_2927_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref_known(v___x_2929_, 1);
v_c_2840_ = v_k_2928_;
goto _start;
}
else
{
lean_dec_ref(v_k_2928_);
lean_dec_ref(v_f_2839_);
return v___x_2929_;
}
}
default: 
{
lean_object* v_decl_2931_; lean_object* v_k_2932_; lean_object* v_params_2933_; lean_object* v_type_2934_; lean_object* v_value_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_decl_2931_ = lean_ctor_get(v_c_2840_, 0);
lean_inc_ref(v_decl_2931_);
v_k_2932_ = lean_ctor_get(v_c_2840_, 1);
lean_inc_ref(v_k_2932_);
lean_dec_ref(v_c_2840_);
v_params_2933_ = lean_ctor_get(v_decl_2931_, 2);
lean_inc_ref(v_params_2933_);
v_type_2934_ = lean_ctor_get(v_decl_2931_, 3);
lean_inc_ref(v_type_2934_);
v_value_2935_ = lean_ctor_get(v_decl_2931_, 4);
lean_inc_ref(v_value_2935_);
lean_dec_ref(v_decl_2931_);
v___x_2936_ = lean_unsigned_to_nat(0u);
v___x_2937_ = lean_array_get_size(v_params_2933_);
v___x_2938_ = lean_nat_dec_lt(v___x_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
lean_dec_ref(v_params_2933_);
lean_inc_ref(v_f_2839_);
v___x_2939_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2839_, v_type_2934_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2940_; 
lean_dec_ref_known(v___x_2939_, 1);
lean_inc_ref(v_f_2839_);
v___x_2940_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2838_, v_f_2839_, v_value_2935_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_dec_ref_known(v___x_2940_, 1);
v_c_2840_ = v_k_2932_;
goto _start;
}
else
{
lean_dec_ref(v_k_2932_);
lean_dec_ref(v_f_2839_);
return v___x_2940_;
}
}
else
{
lean_dec_ref(v_value_2935_);
lean_dec_ref(v_k_2932_);
lean_dec_ref(v_f_2839_);
return v___x_2939_;
}
}
else
{
lean_object* v___x_2942_; size_t v___x_2943_; size_t v___x_2944_; lean_object* v___x_2945_; 
v___x_2942_ = lean_box(0);
v___x_2943_ = ((size_t)0ULL);
v___x_2944_ = lean_usize_of_nat(v___x_2937_);
lean_inc_ref(v_f_2839_);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2838_, v_f_2839_, v_params_2933_, v___x_2943_, v___x_2944_, v___x_2942_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v_params_2933_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v___x_2946_; 
lean_dec_ref_known(v___x_2945_, 1);
lean_inc_ref(v_f_2839_);
v___x_2946_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2839_, v_type_2934_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v___x_2947_; 
lean_dec_ref_known(v___x_2946_, 1);
lean_inc_ref(v_f_2839_);
v___x_2947_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2838_, v_f_2839_, v_value_2935_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_dec_ref_known(v___x_2947_, 1);
v_c_2840_ = v_k_2932_;
goto _start;
}
else
{
lean_dec_ref(v_k_2932_);
lean_dec_ref(v_f_2839_);
return v___x_2947_;
}
}
else
{
lean_dec_ref(v_value_2935_);
lean_dec_ref(v_k_2932_);
lean_dec_ref(v_f_2839_);
return v___x_2946_;
}
}
else
{
lean_dec_ref(v_value_2935_);
lean_dec_ref(v_type_2934_);
lean_dec_ref(v_k_2932_);
lean_dec_ref(v_f_2839_);
return v___x_2945_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2838_ = stack[0].m_num;
lean_object* v_f_2839_ = stack[1].m_obj;
lean_object* v_c_2840_ = stack[2].m_obj;
lean_object* v___y_2841_ = stack[3].m_obj;
lean_object* v___y_2842_ = stack[4].m_obj;
lean_object* v___y_2843_ = stack[5].m_obj;
lean_object* v___y_2844_ = stack[6].m_obj;
lean_object* v___y_2845_ = stack[7].m_obj;
lean_object* v___y_2846_ = stack[8].m_obj;
lean_object* v_res_2949_;
v_res_2949_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2838_, v_f_2839_, v_c_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
stack->m_obj
 = v_res_2949_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(uint8_t v_pu_2950_, lean_object* v_f_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2950_, v_f_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2950_ = stack[0].m_num;
lean_object* v_f_2951_ = stack[1].m_obj;
lean_object* v___y_2952_ = stack[2].m_obj;
lean_object* v___y_2953_ = stack[3].m_obj;
lean_object* v___y_2954_ = stack[4].m_obj;
lean_object* v___y_2955_ = stack[5].m_obj;
lean_object* v___y_2956_ = stack[6].m_obj;
lean_object* v___y_2957_ = stack[7].m_obj;
lean_object* v___y_2958_ = stack[8].m_obj;
lean_object* v_res_2961_;
v_res_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_2950_, v_f_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
stack->m_obj
 = v_res_2961_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(lean_object* v_pu_2962_, lean_object* v_f_2963_, lean_object* v_as_2964_, lean_object* v_i_2965_, lean_object* v_stop_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v_pu_boxed_2975_; size_t v_i_boxed_2976_; size_t v_stop_boxed_2977_; lean_object* v_res_2978_; 
v_pu_boxed_2975_ = lean_unbox(v_pu_2962_);
v_i_boxed_2976_ = lean_unbox_usize(v_i_2965_);
lean_dec(v_i_2965_);
v_stop_boxed_2977_ = lean_unbox_usize(v_stop_2966_);
lean_dec(v_stop_2966_);
v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_2975_, v_f_2963_, v_as_2964_, v_i_boxed_2976_, v_stop_boxed_2977_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v_as_2964_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(lean_object* v_pu_2979_, lean_object* v_f_2980_, lean_object* v_c_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_pu_boxed_2989_; lean_object* v_res_2990_; 
v_pu_boxed_2989_ = lean_unbox(v_pu_2979_);
v_res_2990_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_2989_, v_f_2980_, v_c_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
return v_res_2990_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(uint8_t v_pu_2991_, lean_object* v_f_2992_, lean_object* v_decl_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_params_3001_; lean_object* v_type_3002_; lean_object* v_value_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_params_3001_ = lean_ctor_get(v_decl_2993_, 2);
lean_inc_ref(v_params_3001_);
v_type_3002_ = lean_ctor_get(v_decl_2993_, 3);
lean_inc_ref(v_type_3002_);
v_value_3003_ = lean_ctor_get(v_decl_2993_, 4);
lean_inc_ref(v_value_3003_);
lean_dec_ref(v_decl_2993_);
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_array_get_size(v_params_3001_);
v___x_3006_ = lean_nat_dec_lt(v___x_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec_ref(v_params_3001_);
lean_inc_ref(v_f_2992_);
v___x_3007_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2992_, v_type_3002_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v___x_3008_; 
lean_dec_ref_known(v___x_3007_, 1);
v___x_3008_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2991_, v_f_2992_, v_value_3003_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
return v___x_3008_;
}
else
{
lean_dec_ref(v_value_3003_);
lean_dec_ref(v_f_2992_);
return v___x_3007_;
}
}
else
{
lean_object* v___x_3009_; size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = lean_usize_of_nat(v___x_3005_);
lean_inc_ref(v_f_2992_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_2991_, v_f_2992_, v_params_3001_, v___x_3010_, v___x_3011_, v___x_3009_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec_ref(v_params_3001_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v___x_3013_; 
lean_dec_ref_known(v___x_3012_, 1);
lean_inc_ref(v_f_2992_);
v___x_3013_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_2992_, v_type_3002_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; 
lean_dec_ref_known(v___x_3013_, 1);
v___x_3014_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_2991_, v_f_2992_, v_value_3003_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
return v___x_3014_;
}
else
{
lean_dec_ref(v_value_3003_);
lean_dec_ref(v_f_2992_);
return v___x_3013_;
}
}
else
{
lean_dec_ref(v_value_3003_);
lean_dec_ref(v_type_3002_);
lean_dec_ref(v_f_2992_);
return v___x_3012_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2991_ = stack[0].m_num;
lean_object* v_f_2992_ = stack[1].m_obj;
lean_object* v_decl_2993_ = stack[2].m_obj;
lean_object* v___y_2994_ = stack[3].m_obj;
lean_object* v___y_2995_ = stack[4].m_obj;
lean_object* v___y_2996_ = stack[5].m_obj;
lean_object* v___y_2997_ = stack[6].m_obj;
lean_object* v___y_2998_ = stack[7].m_obj;
lean_object* v___y_2999_ = stack[8].m_obj;
lean_object* v_res_3015_;
v_res_3015_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_2991_, v_f_2992_, v_decl_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
stack->m_obj
 = v_res_3015_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(lean_object* v_pu_3016_, lean_object* v_f_3017_, lean_object* v_decl_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
uint8_t v_pu_boxed_3026_; lean_object* v_res_3027_; 
v_pu_boxed_3026_ = lean_unbox(v_pu_3016_);
v_res_3027_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_3026_, v_f_3017_, v_decl_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec(v___y_3019_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(lean_object* v_msg_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_box(0);
v___x_3030_ = lean_panic_fn_borrowed(v___x_3029_, v_msg_3028_);
return v___x_3030_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3034_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2));
v___x_3035_ = lean_unsigned_to_nat(11u);
v___x_3036_ = lean_unsigned_to_nat(163u);
v___x_3037_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1));
v___x_3038_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0));
v___x_3039_ = l_mkPanicMessageWithDecl(v___x_3038_, v___x_3037_, v___x_3036_, v___x_3035_, v___x_3034_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(lean_object* v_a_3040_, lean_object* v_x_3041_){
_start:
{
if (lean_obj_tag(v_x_3041_) == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3043_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_3042_);
return v___x_3043_;
}
else
{
lean_object* v_key_3044_; lean_object* v_value_3045_; lean_object* v_tail_3046_; uint8_t v___x_3047_; 
v_key_3044_ = lean_ctor_get(v_x_3041_, 0);
v_value_3045_ = lean_ctor_get(v_x_3041_, 1);
v_tail_3046_ = lean_ctor_get(v_x_3041_, 2);
v___x_3047_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_3044_, v_a_3040_);
if (v___x_3047_ == 0)
{
v_x_3041_ = v_tail_3046_;
goto _start;
}
else
{
lean_inc(v_value_3045_);
return v_value_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(lean_object* v_a_3049_, lean_object* v_x_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3049_, v_x_3050_);
lean_dec(v_x_3050_);
lean_dec(v_a_3049_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* v_m_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_buckets_3054_; lean_object* v___x_3055_; uint64_t v___x_3056_; uint64_t v___x_3057_; uint64_t v___x_3058_; uint64_t v_fold_3059_; uint64_t v___x_3060_; uint64_t v___x_3061_; uint64_t v___x_3062_; size_t v___x_3063_; size_t v___x_3064_; size_t v___x_3065_; size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_buckets_3054_ = lean_ctor_get(v_m_3052_, 1);
v___x_3055_ = lean_array_get_size(v_buckets_3054_);
v___x_3056_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_3053_);
v___x_3057_ = 32ULL;
v___x_3058_ = lean_uint64_shift_right(v___x_3056_, v___x_3057_);
v_fold_3059_ = lean_uint64_xor(v___x_3056_, v___x_3058_);
v___x_3060_ = 16ULL;
v___x_3061_ = lean_uint64_shift_right(v_fold_3059_, v___x_3060_);
v___x_3062_ = lean_uint64_xor(v_fold_3059_, v___x_3061_);
v___x_3063_ = lean_uint64_to_usize(v___x_3062_);
v___x_3064_ = lean_usize_of_nat(v___x_3055_);
v___x_3065_ = ((size_t)1ULL);
v___x_3066_ = lean_usize_sub(v___x_3064_, v___x_3065_);
v___x_3067_ = lean_usize_land(v___x_3063_, v___x_3066_);
v___x_3068_ = lean_array_uget_borrowed(v_buckets_3054_, v___x_3067_);
v___x_3069_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_3053_, v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* v_m_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_3070_, v_a_3071_);
lean_dec(v_a_3071_);
lean_dec_ref(v_m_3070_);
return v_res_3072_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* v_decl_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v___y_3083_; uint8_t v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = 0;
v___x_3109_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0));
switch(lean_obj_tag(v_decl_3074_))
{
case 0:
{
lean_object* v_decl_3110_; lean_object* v___x_3111_; 
v_decl_3110_ = lean_ctor_get(v_decl_3074_, 0);
lean_inc_ref(v_decl_3110_);
v___x_3111_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3108_, v___x_3109_, v_decl_3110_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
v___y_3083_ = v___x_3111_;
goto v___jp_3082_;
}
case 1:
{
lean_object* v_decl_3112_; lean_object* v___x_3113_; 
v_decl_3112_ = lean_ctor_get(v_decl_3074_, 0);
lean_inc_ref(v_decl_3112_);
v___x_3113_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3108_, v___x_3109_, v_decl_3112_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
v___y_3083_ = v___x_3113_;
goto v___jp_3082_;
}
case 2:
{
lean_object* v_decl_3114_; lean_object* v___x_3115_; 
v_decl_3114_ = lean_ctor_get(v_decl_3074_, 0);
lean_inc_ref(v_decl_3114_);
v___x_3115_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3108_, v___x_3109_, v_decl_3114_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
v___y_3083_ = v___x_3115_;
goto v___jp_3082_;
}
case 3:
{
lean_object* v_fvarId_3116_; lean_object* v_y_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_fvarId_3116_ = lean_ctor_get(v_decl_3074_, 0);
v_y_3117_ = lean_ctor_get(v_decl_3074_, 2);
lean_inc(v_fvarId_3116_);
v___x_3118_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3116_, v_a_3075_);
lean_dec_ref(v___x_3118_);
lean_inc(v_y_3117_);
v___x_3119_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_3109_, v_y_3117_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
v___y_3083_ = v___x_3119_;
goto v___jp_3082_;
}
case 4:
{
lean_object* v_fvarId_3120_; lean_object* v_y_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_fvarId_3120_ = lean_ctor_get(v_decl_3074_, 0);
v_y_3121_ = lean_ctor_get(v_decl_3074_, 2);
lean_inc(v_fvarId_3120_);
v___x_3122_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3120_, v_a_3075_);
lean_dec_ref(v___x_3122_);
lean_inc(v_y_3121_);
v___x_3123_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3121_, v_a_3075_);
v___y_3083_ = v___x_3123_;
goto v___jp_3082_;
}
case 5:
{
lean_object* v_fvarId_3124_; lean_object* v_y_3125_; lean_object* v_ty_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_fvarId_3124_ = lean_ctor_get(v_decl_3074_, 0);
v_y_3125_ = lean_ctor_get(v_decl_3074_, 3);
v_ty_3126_ = lean_ctor_get(v_decl_3074_, 4);
lean_inc(v_fvarId_3124_);
v___x_3127_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3124_, v_a_3075_);
lean_dec_ref(v___x_3127_);
lean_inc(v_y_3125_);
v___x_3128_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_3125_, v_a_3075_);
lean_dec_ref(v___x_3128_);
lean_inc_ref(v_ty_3126_);
v___x_3129_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_3109_, v_ty_3126_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
v___y_3083_ = v___x_3129_;
goto v___jp_3082_;
}
default: 
{
lean_object* v_fvarId_3130_; lean_object* v___x_3131_; 
v_fvarId_3130_ = lean_ctor_get(v_decl_3074_, 0);
lean_inc(v_fvarId_3130_);
v___x_3131_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_3130_, v_a_3075_);
v___y_3083_ = v___x_3131_;
goto v___jp_3082_;
}
}
v___jp_3082_:
{
if (lean_obj_tag(v___y_3083_) == 0)
{
lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3106_; 
v_isSharedCheck_3106_ = !lean_is_exclusive(v___y_3083_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v___y_3083_, 0);
lean_dec(v_unused_3107_);
v___x_3085_ = v___y_3083_;
v_isShared_3086_ = v_isSharedCheck_3106_;
goto v_resetjp_3084_;
}
else
{
lean_dec(v___y_3083_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3106_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v_decision_3088_; lean_object* v_newArms_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3105_; 
v___x_3087_ = lean_st_ref_take(v_a_3075_);
v_decision_3088_ = lean_ctor_get(v___x_3087_, 0);
v_newArms_3089_ = lean_ctor_get(v___x_3087_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3091_ = v___x_3087_;
v_isShared_3092_ = v_isSharedCheck_3105_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_newArms_3089_);
lean_inc(v_decision_3088_);
lean_dec(v___x_3087_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3105_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_box(2);
v___x_3095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3089_, v___x_3094_);
v___x_3096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3096_, 0, v_decl_3074_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3089_, v___x_3094_, v___x_3096_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___x_3097_);
v___x_3099_ = v___x_3091_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_decision_3088_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3100_ = lean_st_ref_put(v_a_3075_, v___x_3099_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3093_);
v___x_3102_ = v___x_3085_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3093_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_3074_);
return v___y_3083_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3074_ = stack[0].m_obj;
lean_object* v_a_3075_ = stack[1].m_obj;
lean_object* v_a_3076_ = stack[2].m_obj;
lean_object* v_a_3077_ = stack[3].m_obj;
lean_object* v_a_3078_ = stack[4].m_obj;
lean_object* v_a_3079_ = stack[5].m_obj;
lean_object* v_a_3080_ = stack[6].m_obj;
lean_object* v_res_3132_;
v_res_3132_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
stack->m_obj
 = v_res_3132_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(lean_object* v_decl_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_decl_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec(v_a_3134_);
return v_res_3141_;
}
}
lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(uint8_t v_pu_3142_, lean_object* v_f_3143_, lean_object* v_arg_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_3143_, v_arg_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3152_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3142_ = stack[0].m_num;
lean_object* v_f_3143_ = stack[1].m_obj;
lean_object* v_arg_3144_ = stack[2].m_obj;
lean_object* v___y_3145_ = stack[3].m_obj;
lean_object* v___y_3146_ = stack[4].m_obj;
lean_object* v___y_3147_ = stack[5].m_obj;
lean_object* v___y_3148_ = stack[6].m_obj;
lean_object* v___y_3149_ = stack[7].m_obj;
lean_object* v___y_3150_ = stack[8].m_obj;
lean_object* v_res_3153_;
v_res_3153_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_3142_, v_f_3143_, v_arg_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
stack->m_obj
 = v_res_3153_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(lean_object* v_pu_3154_, lean_object* v_f_3155_, lean_object* v_arg_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_pu_boxed_3164_; lean_object* v_res_3165_; 
v_pu_boxed_3164_ = lean_unbox(v_pu_3154_);
v_res_3165_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(v_pu_boxed_3164_, v_f_3155_, v_arg_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec(v___y_3157_);
return v_res_3165_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(uint8_t v_pu_3166_, lean_object* v_f_3167_, lean_object* v_param_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_3167_, v_param_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3166_ = stack[0].m_num;
lean_object* v_f_3167_ = stack[1].m_obj;
lean_object* v_param_3168_ = stack[2].m_obj;
lean_object* v___y_3169_ = stack[3].m_obj;
lean_object* v___y_3170_ = stack[4].m_obj;
lean_object* v___y_3171_ = stack[5].m_obj;
lean_object* v___y_3172_ = stack[6].m_obj;
lean_object* v___y_3173_ = stack[7].m_obj;
lean_object* v___y_3174_ = stack[8].m_obj;
lean_object* v_res_3177_;
v_res_3177_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_3166_, v_f_3167_, v_param_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
stack->m_obj
 = v_res_3177_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(lean_object* v_pu_3178_, lean_object* v_f_3179_, lean_object* v_param_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v_pu_boxed_3188_; lean_object* v_res_3189_; 
v_pu_boxed_3188_ = lean_unbox(v_pu_3178_);
v_res_3189_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_3188_, v_f_3179_, v_param_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
return v_res_3189_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(uint8_t v_pu_3190_, lean_object* v_alt_3191_, lean_object* v_f_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_3191_, v_f_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3190_ = stack[0].m_num;
lean_object* v_alt_3191_ = stack[1].m_obj;
lean_object* v_f_3192_ = stack[2].m_obj;
lean_object* v___y_3193_ = stack[3].m_obj;
lean_object* v___y_3194_ = stack[4].m_obj;
lean_object* v___y_3195_ = stack[5].m_obj;
lean_object* v___y_3196_ = stack[6].m_obj;
lean_object* v___y_3197_ = stack[7].m_obj;
lean_object* v___y_3198_ = stack[8].m_obj;
lean_object* v_res_3201_;
v_res_3201_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_3190_, v_alt_3191_, v_f_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
stack->m_obj
 = v_res_3201_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(lean_object* v_pu_3202_, lean_object* v_alt_3203_, lean_object* v_f_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v_pu_boxed_3212_; lean_object* v_res_3213_; 
v_pu_boxed_3212_ = lean_unbox(v_pu_3202_);
v_res_3213_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_3212_, v_alt_3203_, v_f_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec(v___y_3205_);
return v_res_3213_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* v_fvar_3214_, lean_object* v_arm_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3218_; lean_object* v_decision_3235_; lean_object* v___x_3236_; 
v___x_3218_ = lean_st_ref_get(v_a_3216_);
v_decision_3235_ = lean_ctor_get(v___x_3218_, 0);
lean_inc_ref(v_decision_3235_);
lean_dec(v___x_3218_);
v___x_3236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_3235_, v_fvar_3214_);
lean_dec_ref(v_decision_3235_);
if (lean_obj_tag(v___x_3236_) == 1)
{
lean_object* v_val_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3264_; 
v_val_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3264_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_val_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3264_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = lean_box(3);
v___x_3242_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3237_, v___x_3241_);
if (v___x_3242_ == 0)
{
uint8_t v___x_3243_; 
v___x_3243_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_3237_, v_arm_3215_);
lean_dec(v_arm_3215_);
lean_dec(v_val_3237_);
if (v___x_3243_ == 0)
{
lean_del_object(v___x_3239_);
goto v___jp_3219_;
}
else
{
if (v___x_3242_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_dec(v_fvar_3214_);
v___x_3244_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3244_);
v___x_3246_ = v___x_3239_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
else
{
lean_del_object(v___x_3239_);
goto v___jp_3219_;
}
}
}
else
{
lean_object* v___x_3248_; lean_object* v_decision_3249_; lean_object* v_newArms_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_val_3237_);
v___x_3248_ = lean_st_ref_take(v_a_3216_);
v_decision_3249_ = lean_ctor_get(v___x_3248_, 0);
v_newArms_3250_ = lean_ctor_get(v___x_3248_, 1);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3252_ = v___x_3248_;
v_isShared_3253_ = v_isSharedCheck_3263_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_newArms_3250_);
lean_inc(v_decision_3249_);
lean_dec(v___x_3248_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3263_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3254_ = lean_box(0);
v___x_3255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3249_, v_fvar_3214_, v_arm_3215_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3255_);
v___x_3257_ = v___x_3252_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_newArms_3250_);
v___x_3257_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = lean_st_ref_put(v_a_3216_, v___x_3257_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3254_);
v___x_3260_ = v___x_3239_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3254_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v___x_3236_);
lean_dec(v_arm_3215_);
lean_dec(v_fvar_3214_);
v___x_3265_ = lean_box(0);
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
return v___x_3266_;
}
v___jp_3219_:
{
lean_object* v___x_3220_; lean_object* v_decision_3221_; lean_object* v_newArms_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3234_; 
v___x_3220_ = lean_st_ref_take(v_a_3216_);
v_decision_3221_ = lean_ctor_get(v___x_3220_, 0);
v_newArms_3222_ = lean_ctor_get(v___x_3220_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3224_ = v___x_3220_;
v_isShared_3225_ = v_isSharedCheck_3234_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_newArms_3222_);
lean_inc(v_decision_3221_);
lean_dec(v___x_3220_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3234_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_box(2);
v___x_3228_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_3221_, v_fvar_3214_, v___x_3227_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3228_);
v___x_3230_ = v___x_3224_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_newArms_3222_);
v___x_3230_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_st_ref_put(v_a_3216_, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3226_);
return v___x_3232_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_3214_ = stack[0].m_obj;
lean_object* v_arm_3215_ = stack[1].m_obj;
lean_object* v_a_3216_ = stack[2].m_obj;
lean_object* v_res_3267_;
v_res_3267_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3214_, v_arm_3215_, v_a_3216_);
stack->m_obj
 = v_res_3267_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* v_fvar_3268_, lean_object* v_arm_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3268_, v_arm_3269_, v_a_3270_);
lean_dec(v_a_3270_);
return v_res_3272_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* v_fvar_3273_, lean_object* v_arm_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_3273_, v_arm_3274_, v_a_3275_);
return v___x_3282_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_3273_ = stack[0].m_obj;
lean_object* v_arm_3274_ = stack[1].m_obj;
lean_object* v_a_3275_ = stack[2].m_obj;
lean_object* v_a_3276_ = stack[3].m_obj;
lean_object* v_a_3277_ = stack[4].m_obj;
lean_object* v_a_3278_ = stack[5].m_obj;
lean_object* v_a_3279_ = stack[6].m_obj;
lean_object* v_a_3280_ = stack[7].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3273_, v_arm_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* v_fvar_3284_, lean_object* v_arm_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(v_fvar_3284_, v_arm_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec(v_a_3286_);
return v_res_3293_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* v___x_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_3295_, v___x_3294_, v___y_3296_);
return v___x_3303_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3294_ = stack[0].m_obj;
lean_object* v_x_3295_ = stack[1].m_obj;
lean_object* v___y_3296_ = stack[2].m_obj;
lean_object* v___y_3297_ = stack[3].m_obj;
lean_object* v___y_3298_ = stack[4].m_obj;
lean_object* v___y_3299_ = stack[5].m_obj;
lean_object* v___y_3300_ = stack[6].m_obj;
lean_object* v___y_3301_ = stack[7].m_obj;
lean_object* v_res_3304_;
v_res_3304_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3294_, v_x_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
stack->m_obj
 = v_res_3304_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* v___x_3305_, lean_object* v_x_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(v___x_3305_, v_x_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___y_3307_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(lean_object* v_msg_3315_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default));
v___x_3317_ = lean_panic_fn_borrowed(v___x_3316_, v_msg_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(lean_object* v_a_3318_, lean_object* v_x_3319_){
_start:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
v___x_3321_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_3320_);
return v___x_3321_;
}
else
{
lean_object* v_key_3322_; lean_object* v_value_3323_; lean_object* v_tail_3324_; uint8_t v___x_3325_; 
v_key_3322_ = lean_ctor_get(v_x_3319_, 0);
v_value_3323_ = lean_ctor_get(v_x_3319_, 1);
v_tail_3324_ = lean_ctor_get(v_x_3319_, 2);
v___x_3325_ = l_Lean_instBEqFVarId_beq(v_key_3322_, v_a_3318_);
if (v___x_3325_ == 0)
{
v_x_3319_ = v_tail_3324_;
goto _start;
}
else
{
lean_inc(v_value_3323_);
return v_value_3323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(lean_object* v_a_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3327_, v_x_3328_);
lean_dec(v_x_3328_);
lean_dec(v_a_3327_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* v_m_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_buckets_3332_; lean_object* v___x_3333_; uint64_t v___x_3334_; uint64_t v___x_3335_; uint64_t v___x_3336_; uint64_t v_fold_3337_; uint64_t v___x_3338_; uint64_t v___x_3339_; uint64_t v___x_3340_; size_t v___x_3341_; size_t v___x_3342_; size_t v___x_3343_; size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_buckets_3332_ = lean_ctor_get(v_m_3330_, 1);
v___x_3333_ = lean_array_get_size(v_buckets_3332_);
v___x_3334_ = l_Lean_instHashableFVarId_hash(v_a_3331_);
v___x_3335_ = 32ULL;
v___x_3336_ = lean_uint64_shift_right(v___x_3334_, v___x_3335_);
v_fold_3337_ = lean_uint64_xor(v___x_3334_, v___x_3336_);
v___x_3338_ = 16ULL;
v___x_3339_ = lean_uint64_shift_right(v_fold_3337_, v___x_3338_);
v___x_3340_ = lean_uint64_xor(v_fold_3337_, v___x_3339_);
v___x_3341_ = lean_uint64_to_usize(v___x_3340_);
v___x_3342_ = lean_usize_of_nat(v___x_3333_);
v___x_3343_ = ((size_t)1ULL);
v___x_3344_ = lean_usize_sub(v___x_3342_, v___x_3343_);
v___x_3345_ = lean_usize_land(v___x_3341_, v___x_3344_);
v___x_3346_ = lean_array_uget_borrowed(v_buckets_3332_, v___x_3345_);
v___x_3347_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_3331_, v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* v_m_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_3348_, v_a_3349_);
lean_dec(v_a_3349_);
lean_dec_ref(v_m_3348_);
return v_res_3350_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* v_decl_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___x_3359_; lean_object* v_decision_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3417_; 
v___x_3359_ = lean_st_ref_get(v_a_3352_);
v_decision_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3359_, 1);
lean_dec(v_unused_3418_);
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3417_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_decision_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3417_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___y_3368_; lean_object* v___f_3394_; 
v___x_3364_ = 0;
v___x_3365_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_3351_);
v___x_3366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3360_, v___x_3365_);
lean_dec(v___x_3365_);
lean_dec_ref(v_decision_3360_);
lean_inc(v___x_3366_);
v___f_3394_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3394_, 0, v___x_3366_);
switch(lean_obj_tag(v_decl_3351_))
{
case 0:
{
lean_object* v_decl_3395_; lean_object* v___x_3396_; 
v_decl_3395_ = lean_ctor_get(v_decl_3351_, 0);
lean_inc_ref(v_decl_3395_);
v___x_3396_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_3364_, v___f_3394_, v_decl_3395_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
v___y_3368_ = v___x_3396_;
goto v___jp_3367_;
}
case 1:
{
lean_object* v_decl_3397_; lean_object* v___x_3398_; 
v_decl_3397_ = lean_ctor_get(v_decl_3351_, 0);
lean_inc_ref(v_decl_3397_);
v___x_3398_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3364_, v___f_3394_, v_decl_3397_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
v___y_3368_ = v___x_3398_;
goto v___jp_3367_;
}
case 2:
{
lean_object* v_decl_3399_; lean_object* v___x_3400_; 
v_decl_3399_ = lean_ctor_get(v_decl_3351_, 0);
lean_inc_ref(v_decl_3399_);
v___x_3400_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_3364_, v___f_3394_, v_decl_3399_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
v___y_3368_ = v___x_3400_;
goto v___jp_3367_;
}
case 3:
{
lean_object* v_fvarId_3401_; lean_object* v_y_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_fvarId_3401_ = lean_ctor_get(v_decl_3351_, 0);
v_y_3402_ = lean_ctor_get(v_decl_3351_, 2);
lean_inc(v___x_3366_);
lean_inc(v_fvarId_3401_);
v___x_3403_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3401_, v___x_3366_, v_a_3352_);
lean_dec_ref(v___x_3403_);
lean_inc(v_y_3402_);
v___x_3404_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_3394_, v_y_3402_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
v___y_3368_ = v___x_3404_;
goto v___jp_3367_;
}
case 4:
{
lean_object* v_fvarId_3405_; lean_object* v_y_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_dec_ref(v___f_3394_);
v_fvarId_3405_ = lean_ctor_get(v_decl_3351_, 0);
v_y_3406_ = lean_ctor_get(v_decl_3351_, 2);
lean_inc_n(v___x_3366_, 2);
lean_inc(v_fvarId_3405_);
v___x_3407_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3405_, v___x_3366_, v_a_3352_);
lean_dec_ref(v___x_3407_);
lean_inc(v_y_3406_);
v___x_3408_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3406_, v___x_3366_, v_a_3352_);
v___y_3368_ = v___x_3408_;
goto v___jp_3367_;
}
case 5:
{
lean_object* v_fvarId_3409_; lean_object* v_y_3410_; lean_object* v_ty_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_fvarId_3409_ = lean_ctor_get(v_decl_3351_, 0);
v_y_3410_ = lean_ctor_get(v_decl_3351_, 3);
v_ty_3411_ = lean_ctor_get(v_decl_3351_, 4);
lean_inc_n(v___x_3366_, 2);
lean_inc(v_fvarId_3409_);
v___x_3412_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3409_, v___x_3366_, v_a_3352_);
lean_dec_ref(v___x_3412_);
lean_inc(v_y_3410_);
v___x_3413_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_3410_, v___x_3366_, v_a_3352_);
lean_dec_ref(v___x_3413_);
lean_inc_ref(v_ty_3411_);
v___x_3414_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_3394_, v_ty_3411_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
v___y_3368_ = v___x_3414_;
goto v___jp_3367_;
}
default: 
{
lean_object* v_fvarId_3415_; lean_object* v___x_3416_; 
lean_dec_ref(v___f_3394_);
v_fvarId_3415_ = lean_ctor_get(v_decl_3351_, 0);
lean_inc(v___x_3366_);
lean_inc(v_fvarId_3415_);
v___x_3416_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_3415_, v___x_3366_, v_a_3352_);
v___y_3368_ = v___x_3416_;
goto v___jp_3367_;
}
}
v___jp_3367_:
{
if (lean_obj_tag(v___y_3368_) == 0)
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3392_; 
v_isSharedCheck_3392_ = !lean_is_exclusive(v___y_3368_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___y_3368_, 0);
lean_dec(v_unused_3393_);
v___x_3370_ = v___y_3368_;
v_isShared_3371_ = v_isSharedCheck_3392_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v___y_3368_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3392_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v_decision_3373_; lean_object* v_newArms_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3391_; 
v___x_3372_ = lean_st_ref_take(v_a_3352_);
v_decision_3373_ = lean_ctor_get(v___x_3372_, 0);
v_newArms_3374_ = lean_ctor_get(v___x_3372_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3376_ = v___x_3372_;
v_isShared_3377_ = v_isSharedCheck_3391_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_newArms_3374_);
lean_inc(v_decision_3373_);
lean_dec(v___x_3372_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3391_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3378_ = lean_box(0);
v___x_3379_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3374_, v___x_3366_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 1);
lean_ctor_set(v___x_3362_, 1, v___x_3379_);
lean_ctor_set(v___x_3362_, 0, v_decl_3351_);
v___x_3381_ = v___x_3362_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_decl_3351_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_3374_, v___x_3366_, v___x_3381_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v___x_3382_);
v___x_3384_ = v___x_3376_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_decision_3373_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3385_ = lean_st_ref_put(v_a_3352_, v___x_3384_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3378_);
v___x_3387_ = v___x_3370_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3378_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3366_);
lean_del_object(v___x_3362_);
lean_dec_ref(v_decl_3351_);
return v___y_3368_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_float_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3351_ = stack[0].m_obj;
lean_object* v_a_3352_ = stack[1].m_obj;
lean_object* v_a_3353_ = stack[2].m_obj;
lean_object* v_a_3354_ = stack[3].m_obj;
lean_object* v_a_3355_ = stack[4].m_obj;
lean_object* v_a_3356_ = stack[5].m_obj;
lean_object* v_a_3357_ = stack[6].m_obj;
lean_object* v_res_3419_;
v_res_3419_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
stack->m_obj
 = v_res_3419_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(lean_object* v_decl_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_decl_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec(v_a_3421_);
return v_res_3428_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* v_as_x27_3429_, lean_object* v_b_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
if (lean_obj_tag(v_as_x27_3429_) == 0)
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v_b_3430_);
return v___x_3438_;
}
else
{
lean_object* v_head_3439_; lean_object* v_tail_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v_decision_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_head_3439_ = lean_ctor_get(v_as_x27_3429_, 0);
v_tail_3440_ = lean_ctor_get(v_as_x27_3429_, 1);
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_st_ref_get(v___y_3431_);
v_decision_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc_ref(v_decision_3443_);
lean_dec(v___x_3442_);
v___x_3444_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_3439_);
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_3443_, v___x_3444_);
lean_dec(v___x_3444_);
lean_dec_ref(v_decision_3443_);
v___x_3446_ = lean_box(3);
v___x_3447_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3448_ = lean_box(2);
v___x_3449_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v___x_3445_, v___x_3448_);
lean_dec(v___x_3445_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_inc(v_head_3439_);
v___x_3450_ = l_Lean_Compiler_LCNF_FloatLetIn_float(v_head_3439_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_dec_ref_known(v___x_3450_, 1);
v_as_x27_3429_ = v_tail_3440_;
v_b_3430_ = v___x_3441_;
goto _start;
}
else
{
return v___x_3450_;
}
}
else
{
lean_object* v___x_3452_; 
lean_inc(v_head_3439_);
v___x_3452_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(v_head_3439_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_dec_ref_known(v___x_3452_, 1);
v_as_x27_3429_ = v_tail_3440_;
v_b_3430_ = v___x_3441_;
goto _start;
}
else
{
return v___x_3452_;
}
}
}
else
{
uint8_t v___x_3454_; lean_object* v___x_3455_; 
lean_dec(v___x_3445_);
v___x_3454_ = 0;
v___x_3455_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v___x_3454_, v_head_3439_, v___y_3434_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec_ref_known(v___x_3455_, 1);
v_as_x27_3429_ = v_tail_3440_;
v_b_3430_ = v___x_3441_;
goto _start;
}
else
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3429_ = stack[0].m_obj;
lean_object* v_b_3430_ = stack[1].m_obj;
lean_object* v___y_3431_ = stack[2].m_obj;
lean_object* v___y_3432_ = stack[3].m_obj;
lean_object* v___y_3433_ = stack[4].m_obj;
lean_object* v___y_3434_ = stack[5].m_obj;
lean_object* v___y_3435_ = stack[6].m_obj;
lean_object* v___y_3436_ = stack[7].m_obj;
lean_object* v_res_3457_;
v_res_3457_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3429_, v_b_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
stack->m_obj
 = v_res_3457_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(lean_object* v_as_x27_3458_, lean_object* v_b_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3458_, v_b_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v_as_x27_3458_);
return v_res_3467_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_box(0);
v___x_3476_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_3469_, v___x_3475_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v___x_3476_, 0);
lean_dec(v_unused_3484_);
v___x_3478_ = v___x_3476_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_dec(v___x_3476_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3475_);
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3475_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
else
{
return v___x_3476_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3468_ = stack[0].m_obj;
lean_object* v_a_3469_ = stack[1].m_obj;
lean_object* v_a_3470_ = stack[2].m_obj;
lean_object* v_a_3471_ = stack[3].m_obj;
lean_object* v_a_3472_ = stack[4].m_obj;
lean_object* v_a_3473_ = stack[5].m_obj;
lean_object* v_res_3485_;
v_res_3485_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
stack->m_obj
 = v_res_3485_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec(v_a_3486_);
return v_res_3493_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* v_as_3494_, lean_object* v_as_x27_3495_, lean_object* v_b_3496_, lean_object* v_a_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_3495_, v_b_3496_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3494_ = stack[0].m_obj;
lean_object* v_as_x27_3495_ = stack[1].m_obj;
lean_object* v_b_3496_ = stack[2].m_obj;
lean_object* v___y_3498_ = stack[4].m_obj;
lean_object* v___y_3499_ = stack[5].m_obj;
lean_object* v___y_3500_ = stack[6].m_obj;
lean_object* v___y_3501_ = stack[7].m_obj;
lean_object* v___y_3502_ = stack[8].m_obj;
lean_object* v___y_3503_ = stack[9].m_obj;
lean_object* v_res_3506_;
v_res_3506_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_3494_, v_as_x27_3495_, v_b_3496_, lean_box(0), v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
stack->m_obj
 = v_res_3506_;
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
v___x_3519_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3522_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3523_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
lean_ctor_set(v___x_3525_, 2, v___x_3524_);
lean_ctor_set(v___x_3525_, 3, v___x_3524_);
lean_ctor_set(v___x_3525_, 4, v___x_3523_);
lean_ctor_set(v___x_3525_, 5, v___x_3523_);
lean_ctor_set(v___x_3525_, 6, v___x_3523_);
lean_ctor_set(v___x_3525_, 7, v___x_3523_);
lean_ctor_set(v___x_3525_, 8, v___x_3523_);
lean_ctor_set(v___x_3525_, 9, v___x_3523_);
lean_ctor_set(v___x_3525_, 10, v___x_3523_);
lean_ctor_set(v___x_3525_, 11, v___x_3522_);
return v___x_3525_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3526_; double v___x_3527_; 
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = lean_float_of_nat(v___x_3526_);
return v___x_3527_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* v_cls_3531_, lean_object* v_msg_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_ref_3538_; lean_object* v___x_3539_; lean_object* v_env_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v_ref_3538_ = lean_ctor_get(v___y_3535_, 2);
v___x_3539_ = lean_st_ref_get(v___y_3536_);
v_env_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc_ref(v_env_3540_);
lean_dec(v___x_3539_);
v___x_3541_ = lean_st_ref_get(v___y_3534_);
v___x_3542_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3533_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3602_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3545_ = v___x_3542_;
v_isShared_3546_ = v_isSharedCheck_3602_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3602_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v_lctx_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3600_; 
v_lctx_3547_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v___x_3541_, 1);
lean_dec(v_unused_3601_);
v___x_3549_ = v___x_3541_;
v_isShared_3550_ = v_isSharedCheck_3600_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_lctx_3547_);
lean_dec(v___x_3541_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3600_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3551_ = lean_unbox(v_a_3543_);
lean_dec(v_a_3543_);
v___x_3552_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3547_, v___x_3551_);
lean_dec_ref(v_lctx_3547_);
v___x_3553_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3535_);
v___x_3554_ = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
v___x_3555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3555_, 0, v_env_3540_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
lean_ctor_set(v___x_3555_, 2, v___x_3552_);
lean_ctor_set(v___x_3555_, 3, v___x_3553_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set_tag(v___x_3549_, 3);
lean_ctor_set(v___x_3549_, 1, v_msg_3532_);
lean_ctor_set(v___x_3549_, 0, v___x_3555_);
v___x_3557_ = v___x_3549_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_msg_3532_);
v___x_3557_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; lean_object* v_traceState_3559_; lean_object* v_env_3560_; lean_object* v_nextMacroScope_3561_; lean_object* v_ngen_3562_; lean_object* v_auxDeclNGen_3563_; lean_object* v_cache_3564_; lean_object* v_recordedDeps_3565_; lean_object* v_messages_3566_; lean_object* v_infoState_3567_; lean_object* v_snapshotTasks_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3598_; 
v___x_3558_ = lean_st_ref_take(v___y_3536_);
v_traceState_3559_ = lean_ctor_get(v___x_3558_, 4);
v_env_3560_ = lean_ctor_get(v___x_3558_, 0);
v_nextMacroScope_3561_ = lean_ctor_get(v___x_3558_, 1);
v_ngen_3562_ = lean_ctor_get(v___x_3558_, 2);
v_auxDeclNGen_3563_ = lean_ctor_get(v___x_3558_, 3);
v_cache_3564_ = lean_ctor_get(v___x_3558_, 5);
v_recordedDeps_3565_ = lean_ctor_get(v___x_3558_, 6);
v_messages_3566_ = lean_ctor_get(v___x_3558_, 7);
v_infoState_3567_ = lean_ctor_get(v___x_3558_, 8);
v_snapshotTasks_3568_ = lean_ctor_get(v___x_3558_, 9);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3570_ = v___x_3558_;
v_isShared_3571_ = v_isSharedCheck_3598_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_snapshotTasks_3568_);
lean_inc(v_infoState_3567_);
lean_inc(v_messages_3566_);
lean_inc(v_recordedDeps_3565_);
lean_inc(v_cache_3564_);
lean_inc(v_traceState_3559_);
lean_inc(v_auxDeclNGen_3563_);
lean_inc(v_ngen_3562_);
lean_inc(v_nextMacroScope_3561_);
lean_inc(v_env_3560_);
lean_dec(v___x_3558_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3598_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
uint64_t v_tid_3572_; lean_object* v_traces_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3597_; 
v_tid_3572_ = lean_ctor_get_uint64(v_traceState_3559_, sizeof(void*)*1);
v_traces_3573_ = lean_ctor_get(v_traceState_3559_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_traceState_3559_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3575_ = v_traceState_3559_;
v_isShared_3576_ = v_isSharedCheck_3597_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_traces_3573_);
lean_dec(v_traceState_3559_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3597_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; double v___x_3579_; uint8_t v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_box(0);
v___x_3579_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
v___x_3580_ = 0;
v___x_3581_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4));
v___x_3582_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3582_, 0, v_cls_3531_);
lean_ctor_set(v___x_3582_, 1, v___x_3578_);
lean_ctor_set(v___x_3582_, 2, v___x_3581_);
lean_ctor_set_float(v___x_3582_, sizeof(void*)*3, v___x_3579_);
lean_ctor_set_float(v___x_3582_, sizeof(void*)*3 + 8, v___x_3579_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*3 + 16, v___x_3580_);
v___x_3583_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5));
v___x_3584_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3557_);
lean_ctor_set(v___x_3584_, 2, v___x_3583_);
lean_inc(v_ref_3538_);
v___x_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3585_, 0, v_ref_3538_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l_Lean_PersistentArray_push___redArg(v_traces_3573_, v___x_3585_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3586_);
v___x_3588_ = v___x_3575_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3586_);
lean_ctor_set_uint64(v_reuseFailAlloc_3596_, sizeof(void*)*1, v_tid_3572_);
v___x_3588_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 4, v___x_3588_);
v___x_3590_ = v___x_3570_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_env_3560_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_nextMacroScope_3561_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_ngen_3562_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_auxDeclNGen_3563_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3595_, 5, v_cache_3564_);
lean_ctor_set(v_reuseFailAlloc_3595_, 6, v_recordedDeps_3565_);
lean_ctor_set(v_reuseFailAlloc_3595_, 7, v_messages_3566_);
lean_ctor_set(v_reuseFailAlloc_3595_, 8, v_infoState_3567_);
lean_ctor_set(v_reuseFailAlloc_3595_, 9, v_snapshotTasks_3568_);
v___x_3590_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_st_ref_put(v___y_3536_, v___x_3590_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3577_);
v___x_3593_ = v___x_3545_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3577_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
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
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v___x_3541_);
lean_dec_ref(v_env_3540_);
lean_dec_ref(v_msg_3532_);
lean_dec(v_cls_3531_);
v_a_3603_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3542_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3542_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3531_ = stack[0].m_obj;
lean_object* v_msg_3532_ = stack[1].m_obj;
lean_object* v___y_3533_ = stack[2].m_obj;
lean_object* v___y_3534_ = stack[3].m_obj;
lean_object* v___y_3535_ = stack[4].m_obj;
lean_object* v___y_3536_ = stack[5].m_obj;
lean_object* v_res_3611_;
v_res_3611_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3531_, v_msg_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
stack->m_obj
 = v_res_3611_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* v_cls_3612_, lean_object* v_msg_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3612_, v_msg_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
return v_res_3619_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* v_cls_3620_, lean_object* v_msg_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_3620_, v_msg_3621_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
return v___x_3628_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3620_ = stack[0].m_obj;
lean_object* v_msg_3621_ = stack[1].m_obj;
lean_object* v___y_3622_ = stack[2].m_obj;
lean_object* v___y_3623_ = stack[3].m_obj;
lean_object* v___y_3624_ = stack[4].m_obj;
lean_object* v___y_3625_ = stack[5].m_obj;
lean_object* v___y_3626_ = stack[6].m_obj;
lean_object* v_res_3629_;
v_res_3629_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3620_, v_msg_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
stack->m_obj
 = v_res_3629_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* v_cls_3630_, lean_object* v_msg_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_3630_, v_msg_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
return v_res_3638_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3648_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4));
v___x_3649_ = l_Lean_Name_append(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* v_code_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
switch(lean_obj_tag(v_code_3656_))
{
case 0:
{
lean_object* v_decl_3663_; lean_object* v_k_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_decl_3663_ = lean_ctor_get(v_code_3656_, 0);
lean_inc_ref(v_decl_3663_);
v_k_3664_ = lean_ctor_get(v_code_3656_, 1);
lean_inc_ref(v_k_3664_);
lean_dec_ref_known(v_code_3656_, 2);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v_decl_3663_);
v___x_3666_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3666_, 0, v_k_3664_);
v___x_3667_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3665_, v___x_3666_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3667_;
}
case 1:
{
lean_object* v_decl_3668_; lean_object* v_k_3669_; lean_object* v_params_3670_; lean_object* v_type_3671_; lean_object* v_value_3672_; uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v_decl_3668_ = lean_ctor_get(v_code_3656_, 0);
lean_inc_ref(v_decl_3668_);
v_k_3669_ = lean_ctor_get(v_code_3656_, 1);
lean_inc_ref(v_k_3669_);
lean_dec_ref_known(v_code_3656_, 2);
v_params_3670_ = lean_ctor_get(v_decl_3668_, 2);
lean_inc_ref(v_params_3670_);
v_type_3671_ = lean_ctor_get(v_decl_3668_, 3);
lean_inc_ref(v_type_3671_);
v_value_3672_ = lean_ctor_get(v_decl_3668_, 4);
v___x_3673_ = 0;
lean_inc_ref(v_value_3672_);
v___x_3674_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3674_, 0, v_value_3672_);
v___x_3675_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3674_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3695_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3695_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3695_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; 
v___x_3680_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3673_, v_decl_3668_, v_type_3671_, v_params_3670_, v_a_3676_, v_a_3659_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 1);
lean_ctor_set(v___x_3678_, 0, v_a_3681_);
v___x_3683_ = v___x_3678_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3681_);
v___x_3683_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3684_, 0, v_k_3669_);
v___x_3685_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3683_, v___x_3684_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3685_;
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_del_object(v___x_3678_);
lean_dec_ref(v_k_3669_);
v_a_3687_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3680_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3680_);
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
lean_dec_ref(v_type_3671_);
lean_dec_ref(v_params_3670_);
lean_dec_ref(v_k_3669_);
lean_dec_ref(v_decl_3668_);
return v___x_3675_;
}
}
case 2:
{
lean_object* v_decl_3696_; lean_object* v_k_3697_; lean_object* v_params_3698_; lean_object* v_type_3699_; lean_object* v_value_3700_; uint8_t v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_decl_3696_ = lean_ctor_get(v_code_3656_, 0);
lean_inc_ref(v_decl_3696_);
v_k_3697_ = lean_ctor_get(v_code_3656_, 1);
lean_inc_ref(v_k_3697_);
lean_dec_ref_known(v_code_3656_, 2);
v_params_3698_ = lean_ctor_get(v_decl_3696_, 2);
lean_inc_ref(v_params_3698_);
v_type_3699_ = lean_ctor_get(v_decl_3696_, 3);
lean_inc_ref(v_type_3699_);
v_value_3700_ = lean_ctor_get(v_decl_3696_, 4);
v___x_3701_ = 0;
lean_inc_ref(v_value_3700_);
v___x_3702_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3702_, 0, v_value_3700_);
v___x_3703_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3702_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3723_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3723_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3723_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3701_, v_decl_3696_, v_type_3699_, v_params_3698_, v_a_3704_, v_a_3659_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 2);
lean_ctor_set(v___x_3706_, 0, v_a_3709_);
v___x_3711_ = v___x_3706_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3709_);
v___x_3711_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3712_, 0, v_k_3697_);
v___x_3713_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(v___x_3711_, v___x_3712_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3713_;
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_del_object(v___x_3706_);
lean_dec_ref(v_k_3697_);
v_a_3715_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3708_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3708_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_3699_);
lean_dec_ref(v_params_3698_);
lean_dec_ref(v_k_3697_);
lean_dec_ref(v_decl_3696_);
return v___x_3703_;
}
}
case 4:
{
lean_object* v_cases_3724_; lean_object* v___x_3725_; 
v_cases_3724_ = lean_ctor_get(v_code_3656_, 0);
lean_inc_ref_n(v_cases_3724_, 2);
v___x_3725_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(v_cases_3724_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v___x_3727_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_3724_);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_a_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_st_mk_ref(v___x_3728_);
v___x_3730_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_3729_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v___x_3731_; lean_object* v_typeName_3732_; lean_object* v_resultType_3733_; lean_object* v_discr_3734_; lean_object* v_alts_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref_known(v___x_3730_, 1);
v___x_3731_ = lean_st_ref_get(v___x_3729_);
lean_dec(v___x_3729_);
v_typeName_3732_ = lean_ctor_get(v_cases_3724_, 0);
v_resultType_3733_ = lean_ctor_get(v_cases_3724_, 1);
v_discr_3734_ = lean_ctor_get(v_cases_3724_, 2);
v_alts_3735_ = lean_ctor_get(v_cases_3724_, 3);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_cases_3724_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3737_ = v_cases_3724_;
v_isShared_3738_ = v_isSharedCheck_3775_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_alts_3735_);
lean_inc(v_discr_3734_);
lean_inc(v_resultType_3733_);
lean_inc(v_typeName_3732_);
lean_dec(v_cases_3724_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3775_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v_newArms_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_newArms_3739_ = lean_ctor_get(v___x_3731_, 1);
lean_inc_ref(v_newArms_3739_);
lean_dec(v___x_3731_);
v___x_3740_ = lean_box(2);
v___x_3741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_3739_, v___x_3740_);
v___x_3742_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3735_);
v___x_3743_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_3739_, v___x_3742_, v_alts_3735_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec_ref(v_newArms_3739_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3766_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3766_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3766_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___y_3749_; size_t v___x_3760_; size_t v___x_3761_; uint8_t v___x_3762_; 
v___x_3760_ = lean_ptr_addr(v_alts_3735_);
lean_dec_ref(v_alts_3735_);
v___x_3761_ = lean_ptr_addr(v_a_3744_);
v___x_3762_ = lean_usize_dec_eq(v___x_3760_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3755_;
}
else
{
size_t v___x_3763_; uint8_t v___x_3764_; 
v___x_3763_ = lean_ptr_addr(v_resultType_3733_);
v___x_3764_ = lean_usize_dec_eq(v___x_3763_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3755_;
}
else
{
uint8_t v___x_3765_; 
v___x_3765_ = l_Lean_instBEqFVarId_beq(v_discr_3734_, v_discr_3734_);
if (v___x_3765_ == 0)
{
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3755_;
}
else
{
lean_dec(v_a_3744_);
lean_del_object(v___x_3737_);
lean_dec(v_discr_3734_);
lean_dec_ref(v_resultType_3733_);
lean_dec(v_typeName_3732_);
v___y_3749_ = v_code_3656_;
goto v___jp_3748_;
}
}
}
v___jp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3750_ = lean_array_mk(v___x_3741_);
v___x_3751_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_3750_, v___y_3749_);
lean_dec_ref(v___x_3750_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v___x_3751_);
v___x_3753_ = v___x_3746_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
v___jp_3755_:
{
lean_object* v___x_3757_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 3, v_a_3744_);
v___x_3757_ = v___x_3737_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_typeName_3732_);
lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_resultType_3733_);
lean_ctor_set(v_reuseFailAlloc_3759_, 2, v_discr_3734_);
lean_ctor_set(v_reuseFailAlloc_3759_, 3, v_a_3744_);
v___x_3757_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
v___y_3749_ = v___x_3758_;
goto v___jp_3748_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v___x_3741_);
lean_del_object(v___x_3737_);
lean_dec_ref(v_alts_3735_);
lean_dec(v_discr_3734_);
lean_dec_ref(v_resultType_3733_);
lean_dec(v_typeName_3732_);
lean_dec_ref_known(v_code_3656_, 1);
v_a_3767_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3743_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3743_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v___x_3729_);
lean_dec_ref_known(v_code_3656_, 1);
lean_dec_ref(v_cases_3724_);
v_a_3776_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3730_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3730_);
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
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref_known(v_code_3656_, 1);
lean_dec_ref(v_cases_3724_);
v_a_3784_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3725_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3725_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
default: 
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_inc(v_a_3657_);
v___x_3792_ = lean_array_mk(v_a_3657_);
v___x_3793_ = l_Array_reverse___redArg(v___x_3792_);
v___x_3794_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___x_3793_, v_code_3656_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
return v___x_3795_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_3656_ = stack[0].m_obj;
lean_object* v_a_3657_ = stack[1].m_obj;
lean_object* v_a_3658_ = stack[2].m_obj;
lean_object* v_a_3659_ = stack[3].m_obj;
lean_object* v_a_3660_ = stack[4].m_obj;
lean_object* v_a_3661_ = stack[5].m_obj;
lean_object* v_res_3796_;
v_res_3796_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
stack->m_obj
 = v_res_3796_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(lean_object* v_code_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(v_code_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
return v_res_3804_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* v___x_3805_, lean_object* v_i_3806_, lean_object* v_as_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; uint8_t v___x_3815_; 
v___x_3814_ = lean_array_get_size(v_as_3807_);
v___x_3815_ = lean_nat_dec_lt(v_i_3806_, v___x_3814_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; 
lean_dec(v_i_3806_);
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v_as_3807_);
return v___x_3816_;
}
else
{
lean_object* v_toCold_3817_; lean_object* v_options_3818_; lean_object* v_inheritedTraceOptions_3819_; uint8_t v_hasTrace_3820_; lean_object* v_a_3821_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; 
v_toCold_3817_ = lean_ctor_get(v___y_3811_, 0);
v_options_3818_ = lean_ctor_get(v_toCold_3817_, 2);
v_inheritedTraceOptions_3819_ = lean_ctor_get(v_toCold_3817_, 11);
v_hasTrace_3820_ = lean_ctor_get_uint8(v_options_3818_, sizeof(void*)*1);
v_a_3821_ = lean_array_fget_borrowed(v_as_3807_, v_i_3806_);
v___x_3852_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_3821_);
v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_3805_, v___x_3852_);
if (v_hasTrace_3820_ == 0)
{
lean_dec(v___x_3852_);
v___y_3855_ = v___y_3809_;
v___y_3856_ = v___y_3810_;
v___y_3857_ = v___y_3811_;
v___y_3858_ = v___y_3812_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3863_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_3864_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
v___x_3865_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3819_, v_options_3818_, v___x_3864_);
if (v___x_3865_ == 0)
{
lean_dec(v___x_3852_);
v___y_3855_ = v___y_3809_;
v___y_3856_ = v___y_3810_;
v___y_3857_ = v___y_3811_;
v___y_3858_ = v___y_3812_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3866_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v___x_3852_, v___x_3867_);
v___x_3869_ = l_Lean_MessageData_ofFormat(v___x_3868_);
v___x_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3866_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = lean_obj_once(&l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9, &l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once, _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
v___x_3872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3870_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = l_List_lengthTR___redArg(v___x_3853_);
v___x_3874_ = l_Nat_reprFast(v___x_3873_);
v___x_3875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
v___x_3876_ = l_Lean_MessageData_ofFormat(v___x_3875_);
v___x_3877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3872_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
v___x_3878_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_3863_, v___x_3877_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_dec_ref_known(v___x_3878_, 1);
v___y_3855_ = v___y_3809_;
v___y_3856_ = v___y_3810_;
v___y_3857_ = v___y_3811_;
v___y_3858_ = v___y_3812_;
goto v___jp_3854_;
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v___x_3853_);
lean_dec_ref(v_as_3807_);
lean_dec(v_i_3806_);
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
v___jp_3822_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v___y_3823_, v___y_3828_);
lean_dec_ref(v___y_3823_);
v___x_3830_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed), 7, 1);
lean_closure_set(v___x_3830_, 0, v___x_3829_);
v___x_3831_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(v___x_3830_, v___y_3825_, v___y_3824_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3833_; size_t v___x_3834_; size_t v___x_3835_; uint8_t v___x_3836_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
lean_inc(v_a_3821_);
v___x_3833_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3821_, v_a_3832_);
v___x_3834_ = lean_ptr_addr(v_a_3821_);
v___x_3835_ = lean_ptr_addr(v___x_3833_);
v___x_3836_ = lean_usize_dec_eq(v___x_3834_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_unsigned_to_nat(1u);
v___x_3838_ = lean_nat_add(v_i_3806_, v___x_3837_);
v___x_3839_ = lean_array_fset(v_as_3807_, v_i_3806_, v___x_3833_);
lean_dec(v_i_3806_);
v_i_3806_ = v___x_3838_;
v_as_3807_ = v___x_3839_;
goto _start;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
lean_dec_ref(v___x_3833_);
v___x_3841_ = lean_unsigned_to_nat(1u);
v___x_3842_ = lean_nat_add(v_i_3806_, v___x_3841_);
lean_dec(v_i_3806_);
v_i_3806_ = v___x_3842_;
goto _start;
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_as_3807_);
lean_dec(v_i_3806_);
v_a_3844_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3831_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3831_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
v___jp_3854_:
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_array_mk(v___x_3853_);
switch(lean_obj_tag(v_a_3821_))
{
case 0:
{
lean_object* v_code_3860_; 
v_code_3860_ = lean_ctor_get(v_a_3821_, 2);
lean_inc_ref(v_code_3860_);
v___y_3823_ = v___x_3859_;
v___y_3824_ = v___y_3856_;
v___y_3825_ = v___y_3855_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3858_;
v___y_3828_ = v_code_3860_;
goto v___jp_3822_;
}
case 1:
{
lean_object* v_code_3861_; 
v_code_3861_ = lean_ctor_get(v_a_3821_, 1);
lean_inc_ref(v_code_3861_);
v___y_3823_ = v___x_3859_;
v___y_3824_ = v___y_3856_;
v___y_3825_ = v___y_3855_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3858_;
v___y_3828_ = v_code_3861_;
goto v___jp_3822_;
}
default: 
{
lean_object* v_code_3862_; 
v_code_3862_ = lean_ctor_get(v_a_3821_, 0);
lean_inc_ref(v_code_3862_);
v___y_3823_ = v___x_3859_;
v___y_3824_ = v___y_3856_;
v___y_3825_ = v___y_3855_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3858_;
v___y_3828_ = v_code_3862_;
goto v___jp_3822_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3805_ = stack[0].m_obj;
lean_object* v_i_3806_ = stack[1].m_obj;
lean_object* v_as_3807_ = stack[2].m_obj;
lean_object* v___y_3808_ = stack[3].m_obj;
lean_object* v___y_3809_ = stack[4].m_obj;
lean_object* v___y_3810_ = stack[5].m_obj;
lean_object* v___y_3811_ = stack[6].m_obj;
lean_object* v___y_3812_ = stack[7].m_obj;
lean_object* v_res_3887_;
v_res_3887_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3805_, v_i_3806_, v_as_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
stack->m_obj
 = v_res_3887_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* v___x_3888_, lean_object* v_i_3889_, lean_object* v_as_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_3888_, v_i_3889_, v_as_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___x_3888_);
return v_res_3897_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(lean_object* v_f_3898_, lean_object* v_v_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
if (lean_obj_tag(v_v_3899_) == 0)
{
lean_object* v_code_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3930_; 
v_code_3906_ = lean_ctor_get(v_v_3899_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_v_3899_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3908_ = v_v_3899_;
v_isShared_3909_ = v_isSharedCheck_3930_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_code_3906_);
lean_dec(v_v_3899_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3930_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; 
lean_inc(v___y_3904_);
lean_inc_ref(v___y_3903_);
lean_inc(v___y_3902_);
lean_inc_ref(v___y_3901_);
lean_inc(v___y_3900_);
v___x_3910_ = lean_apply_7(v_f_3898_, v_code_3906_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, lean_box(0));
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3921_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3921_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3921_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v_a_3911_);
v___x_3916_ = v___x_3908_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3918_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3916_);
v___x_3918_ = v___x_3913_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_del_object(v___x_3908_);
v_a_3922_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3910_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3910_);
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
else
{
lean_object* v___x_3931_; 
lean_dec_ref(v_f_3898_);
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v_v_3899_);
return v___x_3931_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3898_ = stack[0].m_obj;
lean_object* v_v_3899_ = stack[1].m_obj;
lean_object* v___y_3900_ = stack[2].m_obj;
lean_object* v___y_3901_ = stack[3].m_obj;
lean_object* v___y_3902_ = stack[4].m_obj;
lean_object* v___y_3903_ = stack[5].m_obj;
lean_object* v___y_3904_ = stack[6].m_obj;
lean_object* v_res_3932_;
v_res_3932_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3898_, v_v_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
stack->m_obj
 = v_res_3932_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(lean_object* v_f_3933_, lean_object* v_v_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3933_, v_v_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
return v_res_3941_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(uint8_t v_pu_3942_, lean_object* v_f_3943_, lean_object* v_v_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_3943_, v_v_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
return v___x_3951_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3942_ = stack[0].m_num;
lean_object* v_f_3943_ = stack[1].m_obj;
lean_object* v_v_3944_ = stack[2].m_obj;
lean_object* v___y_3945_ = stack[3].m_obj;
lean_object* v___y_3946_ = stack[4].m_obj;
lean_object* v___y_3947_ = stack[5].m_obj;
lean_object* v___y_3948_ = stack[6].m_obj;
lean_object* v___y_3949_ = stack[7].m_obj;
lean_object* v_res_3952_;
v_res_3952_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_3942_, v_f_3943_, v_v_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
stack->m_obj
 = v_res_3952_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(lean_object* v_pu_3953_, lean_object* v_f_3954_, lean_object* v_v_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
uint8_t v_pu_boxed_3962_; lean_object* v_res_3963_; 
v_pu_boxed_3962_ = lean_unbox(v_pu_3953_);
v_res_3963_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_3962_, v_f_3954_, v_v_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
return v_res_3963_;
}
}
lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* v_decl_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
lean_object* v_toSignature_3971_; lean_object* v_value_3972_; uint8_t v_recursive_3973_; lean_object* v_inlineAttr_x3f_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4000_; 
v_toSignature_3971_ = lean_ctor_get(v_decl_3965_, 0);
v_value_3972_ = lean_ctor_get(v_decl_3965_, 1);
v_recursive_3973_ = lean_ctor_get_uint8(v_decl_3965_, sizeof(void*)*3);
v_inlineAttr_x3f_3974_ = lean_ctor_get(v_decl_3965_, 2);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_decl_3965_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3976_ = v_decl_3965_;
v_isShared_3977_ = v_isSharedCheck_4000_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_inlineAttr_x3f_3974_);
lean_inc(v_value_3972_);
lean_inc(v_toSignature_3971_);
lean_dec(v_decl_3965_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4000_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((lean_object*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0));
v___x_3979_ = lean_box(0);
v___x_3980_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_3978_, v_value_3972_, v___x_3979_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3991_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3991_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3991_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v_a_3981_);
v___x_3986_ = v___x_3976_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_toSignature_3971_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_a_3981_);
lean_ctor_set(v_reuseFailAlloc_3990_, 2, v_inlineAttr_x3f_3974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3990_, sizeof(void*)*3, v_recursive_3973_);
v___x_3986_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3988_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3986_);
v___x_3988_ = v___x_3983_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_del_object(v___x_3976_);
lean_dec(v_inlineAttr_x3f_3974_);
lean_dec_ref(v_toSignature_3971_);
v_a_3992_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3980_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3980_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3965_ = stack[0].m_obj;
lean_object* v_a_3966_ = stack[1].m_obj;
lean_object* v_a_3967_ = stack[2].m_obj;
lean_object* v_a_3968_ = stack[3].m_obj;
lean_object* v_a_3969_ = stack[4].m_obj;
lean_object* v_res_4001_;
v_res_4001_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
stack->m_obj
 = v_res_4001_;
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
lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* v_decl_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(v_decl_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_floatLetIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_4009_ = stack[0].m_obj;
lean_object* v_a_4010_ = stack[1].m_obj;
lean_object* v_a_4011_ = stack[2].m_obj;
lean_object* v_a_4012_ = stack[3].m_obj;
lean_object* v_a_4013_ = stack[4].m_obj;
lean_object* v_res_4016_;
v_res_4016_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
stack->m_obj
 = v_res_4016_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(lean_object* v_decl_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(v_decl_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
return v_res_4023_;
}
}
lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(uint8_t v_phase_4026_, lean_object* v___f_4027_, lean_object* v_occurrence_4028_, lean_object* v_h_4029_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0));
v___x_4031_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_4030_, v_phase_4026_, v___f_4027_, v_occurrence_4028_);
return v___x_4031_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_floatLetIn___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_4026_ = stack[0].m_num;
lean_object* v___f_4027_ = stack[1].m_obj;
lean_object* v_occurrence_4028_ = stack[2].m_obj;
lean_object* v_res_4032_;
v_res_4032_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_4026_, v___f_4027_, v_occurrence_4028_, lean_box(0));
stack->m_obj
 = v_res_4032_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(lean_object* v_phase_4033_, lean_object* v___f_4034_, lean_object* v_occurrence_4035_, lean_object* v_h_4036_){
_start:
{
uint8_t v_phase_boxed_4037_; lean_object* v_res_4038_; 
v_phase_boxed_4037_ = lean_unbox(v_phase_4033_);
v_res_4038_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(v_phase_boxed_4037_, v___f_4034_, v_occurrence_4035_, v_h_4036_);
return v_res_4038_;
}
}
lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t v_phase_4040_, lean_object* v_occurrence_4041_){
_start:
{
lean_object* v___f_4042_; lean_object* v___x_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; lean_object* v___x_4047_; 
v___f_4042_ = ((lean_object*)(l_Lean_Compiler_LCNF_floatLetIn___closed__0));
v___x_4043_ = lean_box(v_phase_4040_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4044_, 0, v___x_4043_);
lean_closure_set(v___f_4044_, 1, v___f_4042_);
lean_closure_set(v___f_4044_, 2, v_occurrence_4041_);
v___x_4045_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_4046_ = 0;
v___x_4047_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_4045_, v_phase_4040_, v___x_4046_, v___f_4044_);
return v___x_4047_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_floatLetIn_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_4040_ = stack[0].m_num;
lean_object* v_occurrence_4041_ = stack[1].m_obj;
lean_object* v_res_4048_;
v_res_4048_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_4040_, v_occurrence_4041_);
stack->m_obj
 = v_res_4048_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* v_phase_4049_, lean_object* v_occurrence_4050_){
_start:
{
uint8_t v_phase_boxed_4051_; lean_object* v_res_4052_; 
v_phase_boxed_4051_ = lean_unbox(v_phase_4049_);
v_res_4052_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_4051_, v_occurrence_4050_);
return v_res_4052_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = lean_unsigned_to_nat(3411573818u);
v___x_4105_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4106_ = l_Lean_Name_num___override(v___x_4105_, v___x_4104_);
return v___x_4106_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4108_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4109_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4110_ = l_Lean_Name_str___override(v___x_4109_, v___x_4108_);
return v___x_4110_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_));
v___x_4113_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4114_ = l_Lean_Name_str___override(v___x_4113_, v___x_4112_);
return v___x_4114_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = lean_unsigned_to_nat(2u);
v___x_4116_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4117_ = l_Lean_Name_num___override(v___x_4116_, v___x_4115_);
return v___x_4117_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4119_ = ((lean_object*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2));
v___x_4120_ = 1;
v___x_4121_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
v___x_4122_ = l_Lean_registerTraceClass(v___x_4119_, v___x_4120_, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4123_;
v_res_4123_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(lean_object* v_a_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
return v_res_4125_;
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
