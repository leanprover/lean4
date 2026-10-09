// Lean compiler output
// Module: Lean.Meta.RecursorInfo
// Imports: public import Lean.Meta.Basic import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_recOnSuffix;
extern lean_object* l_Lean_brecOnSuffix;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringOption___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_motive_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_motive_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_majorType_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_majorType_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "<motive-univ>"};
static const lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0 = (const lean_object*)&l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos = (const lean_object*)&l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "{\n  name           := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  numArgs        := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  numParams      := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  numIndices     := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  numMinors      := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  major          := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  motive         := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  paramsAtMajor  := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  indicesAtMajor := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  produceMotive  := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  type           := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  univs          := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  depElim        := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "  recursive      := "};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16_value;
static const lean_string_object l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_RecursorInfo_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__0 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__0_value;
static const lean_closure_object l_Lean_Meta_RecursorInfo_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__1 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__1_value;
static const lean_closure_object l_Lean_Meta_RecursorInfo_instToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringOption___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__1_value)} };
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__2 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__2_value;
static const lean_closure_object l_Lean_Meta_RecursorInfo_instToString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_RecursorInfo_instToString___lam__0, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__2_value),((lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__1_value),((lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__0_value),((lean_object*)&l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value)} };
static const lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__3 = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_RecursorInfo_instToString = (const lean_object*)&l_Lean_Meta_RecursorInfo_instToString___closed__3_value;
static lean_once_cell_t l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not a recursor"};
static const lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid user defined recursor `"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 129, .m_capacity = 129, .m_length = 128, .m_data = "`, result type must be of the form `C t`, where `C` is a bound variable, and t is a (possibly empty) sequence of bound variables"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed recursor `"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid user defined recursor, `"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 191, .m_capacity = 191, .m_length = 190, .m_data = "` does not support dependent elimination, and position of the major premise was not specified (solution: set attribute `[recursor <pos>]`, where `<pos>` is the position of the major premise)"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "invalid major premise position for user defined recursor, recursor has only "};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " arguments"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`, type of the major premise does not contain the recursor parameter"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`, type of the major premise does not contain the recursor index"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "`, motive result sort must be Prop or `Sort u` where u is a universe level parameter"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "`, major premise type does not contain universe level parameter `"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 221, .m_capacity = 221, .m_length = 220, .m_data = "`, motive must have a type of the form (C : Pi (i : B A), I A i -> Type), where A is a (possibly empty) sequence of variables (aka parameters), (i : B A) is a (possibly empty) telescope (aka indices), and I is a constant"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0 = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "`, type of the major premise must be of the form (I ...), where I is a constant"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___boxed(lean_object**);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, indices must occur before major premise"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value;
static const lean_string_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1_value;
static const lean_string_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2_value;
static const lean_string_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "recursor"};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 29, 106, 40, 200, 118, 31, 85)}};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value;
static const lean_string_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "unexpected attribute argument, numeral expected"};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6;
static const lean_string_object l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "major premise position must be greater than zero"};
static const lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7 = (const lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "recursorAttribute"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 14, 117, 146, 218, 161, 149, 75)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 1, 161, 9, 253, 193, 133, 24)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "user defined recursor, numerical parameter specifies position of the major premise"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recursorAttribute;
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_idx_7_; lean_object* v___x_8_; 
v_idx_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_idx_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_idx_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_motive_elim___redArg(lean_object* v_t_21_, lean_object* v_motive_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_21_, v_motive_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_motive_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_motive_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_25_, v_motive_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_majorType_elim___redArg(lean_object* v_t_29_, lean_object* v_majorType_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_29_, v_majorType_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_majorType_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_majorType_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_33_, v_majorType_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0(lean_object* v_x_38_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v___x_39_; 
v___x_39_ = ((lean_object*)(l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0));
return v___x_39_;
}
else
{
lean_object* v_idx_40_; lean_object* v___x_41_; 
v_idx_40_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_idx_40_);
lean_dec_ref_known(v_x_38_, 1);
v___x_41_ = l_Nat_reprFast(v_idx_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object* v_info_44_){
_start:
{
lean_object* v_paramsPos_45_; lean_object* v___x_46_; 
v_paramsPos_45_ = lean_ctor_get(v_info_44_, 5);
v___x_46_ = l_List_lengthTR___redArg(v_paramsPos_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object* v_info_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_RecursorInfo_numParams(v_info_47_);
lean_dec_ref(v_info_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object* v_info_49_){
_start:
{
lean_object* v_indicesPos_50_; lean_object* v___x_51_; 
v_indicesPos_50_ = lean_ctor_get(v_info_49_, 6);
v___x_51_ = l_List_lengthTR___redArg(v_indicesPos_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object* v_info_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_52_);
lean_dec_ref(v_info_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object* v_info_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_RecursorInfo_numParams(v_info_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object* v_info_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_RecursorInfo_motivePos(v_info_56_);
lean_dec_ref(v_info_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object* v_info_58_){
_start:
{
lean_object* v_majorPos_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_majorPos_59_ = lean_ctor_get(v_info_58_, 4);
v___x_60_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_58_);
v___x_61_ = lean_nat_sub(v_majorPos_59_, v___x_60_);
lean_dec(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object* v_info_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_62_);
lean_dec_ref(v_info_62_);
return v_res_63_;
}
}
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object* v_info_64_, lean_object* v_pos_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = l_Lean_Meta_RecursorInfo_numParams(v_info_64_);
v___x_67_ = lean_nat_dec_le(v_pos_65_, v___x_66_);
lean_dec(v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_64_);
v___x_69_ = lean_nat_dec_le(v___x_68_, v_pos_65_);
lean_dec(v___x_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
else
{
lean_object* v_majorPos_71_; uint8_t v___x_72_; 
v_majorPos_71_ = lean_ctor_get(v_info_64_, 4);
v___x_72_ = lean_nat_dec_le(v_pos_65_, v_majorPos_71_);
if (v___x_72_ == 0)
{
return v___x_69_;
}
else
{
return v___x_67_;
}
}
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_RecursorInfo_isMinor_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_64_ = stack[0].m_obj;
lean_object* v_pos_65_ = stack[1].m_obj;
uint8_t v_res_74_;
v_res_74_ = l_Lean_Meta_RecursorInfo_isMinor(v_info_64_, v_pos_65_);
stack->m_num = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object* v_info_75_, lean_object* v_pos_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_Meta_RecursorInfo_isMinor(v_info_75_, v_pos_76_);
lean_dec(v_pos_76_);
lean_dec_ref(v_info_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object* v_info_79_){
_start:
{
lean_object* v_numArgs_80_; lean_object* v_majorPos_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_r_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_numArgs_80_ = lean_ctor_get(v_info_79_, 3);
v_majorPos_81_ = lean_ctor_get(v_info_79_, 4);
v___x_82_ = l_Lean_Meta_RecursorInfo_numParams(v_info_79_);
v___x_83_ = lean_nat_sub(v_numArgs_80_, v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = lean_unsigned_to_nat(1u);
v_r_85_ = lean_nat_sub(v___x_83_, v___x_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_nat_add(v_majorPos_81_, v___x_84_);
v___x_87_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_79_);
v___x_88_ = lean_nat_sub(v___x_86_, v___x_87_);
lean_dec(v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_nat_sub(v_r_85_, v___x_88_);
lean_dec(v___x_88_);
lean_dec(v_r_85_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object* v_info_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Meta_RecursorInfo_numMinors(v_info_90_);
lean_dec_ref(v_info_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0(lean_object* v___f_110_, lean_object* v___f_111_, lean_object* v___f_112_, lean_object* v___f_113_, lean_object* v_info_114_){
_start:
{
lean_object* v_recursorName_115_; lean_object* v_typeName_116_; lean_object* v_univLevelPos_117_; uint8_t v_depElim_118_; uint8_t v_recursive_119_; lean_object* v_numArgs_120_; lean_object* v_majorPos_121_; lean_object* v_paramsPos_122_; lean_object* v_indicesPos_123_; lean_object* v_produceMotive_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___y_198_; 
v_recursorName_115_ = lean_ctor_get(v_info_114_, 0);
v_typeName_116_ = lean_ctor_get(v_info_114_, 1);
v_univLevelPos_117_ = lean_ctor_get(v_info_114_, 2);
v_depElim_118_ = lean_ctor_get_uint8(v_info_114_, sizeof(void*)*8);
v_recursive_119_ = lean_ctor_get_uint8(v_info_114_, sizeof(void*)*8 + 1);
v_numArgs_120_ = lean_ctor_get(v_info_114_, 3);
v_majorPos_121_ = lean_ctor_get(v_info_114_, 4);
lean_inc(v_majorPos_121_);
v_paramsPos_122_ = lean_ctor_get(v_info_114_, 5);
lean_inc(v_paramsPos_122_);
v_indicesPos_123_ = lean_ctor_get(v_info_114_, 6);
lean_inc(v_indicesPos_123_);
v_produceMotive_124_ = lean_ctor_get(v_info_114_, 7);
lean_inc(v_produceMotive_124_);
v___x_125_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0));
v___x_126_ = 1;
lean_inc(v_recursorName_115_);
v___x_127_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_recursorName_115_, v___x_126_);
v___x_128_ = lean_string_append(v___x_125_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1));
v___x_184_ = lean_string_append(v___x_128_, v___x_129_);
v___x_185_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12));
v___x_186_ = lean_string_append(v___x_184_, v___x_185_);
lean_inc(v_typeName_116_);
v___x_187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_typeName_116_, v___x_126_);
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
lean_dec_ref(v___x_187_);
v___x_189_ = lean_string_append(v___x_188_, v___x_129_);
v___x_190_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13));
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
lean_inc(v_univLevelPos_117_);
v___x_192_ = l_List_toString___redArg(v___f_113_, v_univLevelPos_117_);
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
lean_dec_ref(v___x_192_);
v___x_194_ = lean_string_append(v___x_193_, v___x_129_);
v___x_195_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14));
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
if (v_depElim_118_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16));
v___y_198_ = v___x_205_;
goto v___jp_197_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17));
v___y_198_ = v___x_206_;
goto v___jp_197_;
}
v___jp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_133_ = lean_string_append(v___y_131_, v___y_132_);
v___x_134_ = lean_string_append(v___x_133_, v___x_129_);
v___x_135_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2));
v___x_136_ = lean_string_append(v___x_134_, v___x_135_);
lean_inc(v_numArgs_120_);
v___x_137_ = l_Nat_reprFast(v_numArgs_120_);
v___x_138_ = lean_string_append(v___x_136_, v___x_137_);
lean_dec_ref(v___x_137_);
v___x_139_ = lean_string_append(v___x_138_, v___x_129_);
v___x_140_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3));
v___x_141_ = lean_string_append(v___x_139_, v___x_140_);
v___x_142_ = l_Lean_Meta_RecursorInfo_numParams(v_info_114_);
v___x_143_ = l_Nat_reprFast(v___x_142_);
v___x_144_ = lean_string_append(v___x_141_, v___x_143_);
v___x_145_ = lean_string_append(v___x_144_, v___x_129_);
v___x_146_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4));
v___x_147_ = lean_string_append(v___x_145_, v___x_146_);
v___x_148_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_114_);
v___x_149_ = l_Nat_reprFast(v___x_148_);
v___x_150_ = lean_string_append(v___x_147_, v___x_149_);
lean_dec_ref(v___x_149_);
v___x_151_ = lean_string_append(v___x_150_, v___x_129_);
v___x_152_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5));
v___x_153_ = lean_string_append(v___x_151_, v___x_152_);
v___x_154_ = l_Lean_Meta_RecursorInfo_numMinors(v_info_114_);
lean_dec_ref(v_info_114_);
v___x_155_ = l_Nat_reprFast(v___x_154_);
v___x_156_ = lean_string_append(v___x_153_, v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = lean_string_append(v___x_156_, v___x_129_);
v___x_158_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6));
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
v___x_160_ = l_Nat_reprFast(v_majorPos_121_);
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = lean_string_append(v___x_161_, v___x_129_);
v___x_163_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7));
v___x_164_ = lean_string_append(v___x_162_, v___x_163_);
v___x_165_ = lean_string_append(v___x_164_, v___x_143_);
lean_dec_ref(v___x_143_);
v___x_166_ = lean_string_append(v___x_165_, v___x_129_);
v___x_167_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8));
v___x_168_ = lean_string_append(v___x_166_, v___x_167_);
v___x_169_ = l_List_toString___redArg(v___f_110_, v_paramsPos_122_);
v___x_170_ = lean_string_append(v___x_168_, v___x_169_);
lean_dec_ref(v___x_169_);
v___x_171_ = lean_string_append(v___x_170_, v___x_129_);
v___x_172_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9));
v___x_173_ = lean_string_append(v___x_171_, v___x_172_);
v___x_174_ = l_List_toString___redArg(v___f_111_, v_indicesPos_123_);
v___x_175_ = lean_string_append(v___x_173_, v___x_174_);
lean_dec_ref(v___x_174_);
v___x_176_ = lean_string_append(v___x_175_, v___x_129_);
v___x_177_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10));
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = l_List_toString___redArg(v___f_112_, v_produceMotive_124_);
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
lean_dec_ref(v___x_179_);
v___x_181_ = lean_string_append(v___x_180_, v___x_129_);
v___x_182_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11));
v___x_183_ = lean_string_append(v___x_181_, v___x_182_);
return v___x_183_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_string_append(v___x_196_, v___y_198_);
v___x_200_ = lean_string_append(v___x_199_, v___x_129_);
v___x_201_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15));
v___x_202_ = lean_string_append(v___x_200_, v___x_201_);
if (v_recursive_119_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16));
v___y_131_ = v___x_202_;
v___y_132_ = v___x_203_;
goto v___jp_130_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17));
v___y_131_ = v___x_202_;
v___y_132_ = v___x_204_;
goto v___jp_130_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_instMonadEIO___redArg();
return v___x_217_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_toApplicative_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_291_; 
v___x_228_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0);
v___x_229_ = l_StateRefT_x27_instMonad___redArg(v___x_228_);
v_toApplicative_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_229_, 1);
lean_dec(v_unused_292_);
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_291_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_toApplicative_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_291_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_toFunctor_234_; lean_object* v_toSeq_235_; lean_object* v_toSeqLeft_236_; lean_object* v_toSeqRight_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_289_; 
v_toFunctor_234_ = lean_ctor_get(v_toApplicative_230_, 0);
v_toSeq_235_ = lean_ctor_get(v_toApplicative_230_, 2);
v_toSeqLeft_236_ = lean_ctor_get(v_toApplicative_230_, 3);
v_toSeqRight_237_ = lean_ctor_get(v_toApplicative_230_, 4);
v_isSharedCheck_289_ = !lean_is_exclusive(v_toApplicative_230_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v_toApplicative_230_, 1);
lean_dec(v_unused_290_);
v___x_239_ = v_toApplicative_230_;
v_isShared_240_ = v_isSharedCheck_289_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_toSeqRight_237_);
lean_inc(v_toSeqLeft_236_);
lean_inc(v_toSeq_235_);
lean_inc(v_toFunctor_234_);
lean_dec(v_toApplicative_230_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_289_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_250_; 
v___f_241_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1));
v___f_242_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_234_);
v___f_243_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_243_, 0, v_toFunctor_234_);
v___f_244_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_244_, 0, v_toFunctor_234_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___f_243_);
lean_ctor_set(v___x_245_, 1, v___f_244_);
v___f_246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_246_, 0, v_toSeqRight_237_);
v___f_247_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_247_, 0, v_toSeqLeft_236_);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_248_, 0, v_toSeq_235_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 4, v___f_246_);
lean_ctor_set(v___x_239_, 3, v___f_247_);
lean_ctor_set(v___x_239_, 2, v___f_248_);
lean_ctor_set(v___x_239_, 1, v___f_241_);
lean_ctor_set(v___x_239_, 0, v___x_245_);
v___x_250_ = v___x_239_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___f_241_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v___f_248_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v___f_247_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v___f_246_);
v___x_250_ = v_reuseFailAlloc_288_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___f_242_);
lean_ctor_set(v___x_232_, 0, v___x_250_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___f_242_);
v___x_252_ = v_reuseFailAlloc_287_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v_toApplicative_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_285_; 
v___x_253_ = l_StateRefT_x27_instMonad___redArg(v___x_252_);
v_toApplicative_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_253_, 1);
lean_dec(v_unused_286_);
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_285_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_toApplicative_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_285_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_toFunctor_258_; lean_object* v_toSeq_259_; lean_object* v_toSeqLeft_260_; lean_object* v_toSeqRight_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_283_; 
v_toFunctor_258_ = lean_ctor_get(v_toApplicative_254_, 0);
v_toSeq_259_ = lean_ctor_get(v_toApplicative_254_, 2);
v_toSeqLeft_260_ = lean_ctor_get(v_toApplicative_254_, 3);
v_toSeqRight_261_ = lean_ctor_get(v_toApplicative_254_, 4);
v_isSharedCheck_283_ = !lean_is_exclusive(v_toApplicative_254_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_dec(v_unused_284_);
v___x_263_ = v_toApplicative_254_;
v_isShared_264_ = v_isSharedCheck_283_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_toSeqRight_261_);
lean_inc(v_toSeqLeft_260_);
lean_inc(v_toSeq_259_);
lean_inc(v_toFunctor_258_);
lean_dec(v_toApplicative_254_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_283_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___f_265_; lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___x_274_; 
v___f_265_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3));
v___f_266_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_258_);
v___f_267_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_267_, 0, v_toFunctor_258_);
v___f_268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_268_, 0, v_toFunctor_258_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___f_267_);
lean_ctor_set(v___x_269_, 1, v___f_268_);
v___f_270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_270_, 0, v_toSeqRight_261_);
v___f_271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_271_, 0, v_toSeqLeft_260_);
v___f_272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_272_, 0, v_toSeq_259_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 4, v___f_270_);
lean_ctor_set(v___x_263_, 3, v___f_271_);
lean_ctor_set(v___x_263_, 2, v___f_272_);
lean_ctor_set(v___x_263_, 1, v___f_265_);
lean_ctor_set(v___x_263_, 0, v___x_269_);
v___x_274_ = v___x_263_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___f_265_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v___f_272_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v___f_271_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v___f_270_);
v___x_274_ = v_reuseFailAlloc_282_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___f_266_);
lean_ctor_set(v___x_256_, 0, v___x_274_);
v___x_276_ = v___x_256_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___f_266_);
v___x_276_ = v_reuseFailAlloc_281_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_2780__overap_279_; lean_object* v___x_280_; 
v___x_277_ = lean_box(0);
v___x_278_ = l_instInhabitedOfMonad___redArg(v___x_276_, v___x_277_);
v___x_2780__overap_279_ = lean_panic_fn_borrowed(v___x_278_, v_msg_222_);
lean_dec(v___x_278_);
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
lean_inc(v___y_224_);
lean_inc_ref(v___y_223_);
v___x_280_ = lean_apply_5(v___x_2780__overap_279_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, lean_box(0));
return v___x_280_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_222_ = stack[0].m_obj;
lean_object* v___y_223_ = stack[1].m_obj;
lean_object* v___y_224_ = stack[2].m_obj;
lean_object* v___y_225_ = stack[3].m_obj;
lean_object* v___y_226_ = stack[4].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v_msg_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___boxed(lean_object* v_msg_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v_msg_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(lean_object* v_msgData_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_env_308_; uint8_t v___x_309_; lean_object* v_env_310_; lean_object* v___x_311_; lean_object* v_toCold_312_; lean_object* v_mctx_313_; lean_object* v_lctx_314_; lean_object* v_options_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v___x_309_ = 0;
v_env_310_ = l_Lean_Environment_setRecordingDeps(v_env_308_, v___x_309_);
v___x_311_ = lean_st_ref_get(v___y_303_);
v_toCold_312_ = lean_ctor_get(v___y_304_, 0);
v_mctx_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_mctx_313_);
lean_dec(v___x_311_);
v_lctx_314_ = lean_ctor_get(v___y_302_, 2);
v_options_315_ = lean_ctor_get(v_toCold_312_, 2);
lean_inc_ref(v_options_315_);
lean_inc_ref(v_lctx_314_);
v___x_316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_316_, 0, v_env_310_);
lean_ctor_set(v___x_316_, 1, v_mctx_313_);
lean_ctor_set(v___x_316_, 2, v_lctx_314_);
lean_ctor_set(v___x_316_, 3, v_options_315_);
v___x_317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_msgData_301_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_301_ = stack[0].m_obj;
lean_object* v___y_302_ = stack[1].m_obj;
lean_object* v___y_303_ = stack[2].m_obj;
lean_object* v___y_304_ = stack[3].m_obj;
lean_object* v___y_305_ = stack[4].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msgData_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msgData_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_ref_333_; lean_object* v___x_334_; lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_ref_333_ = lean_ctor_get(v___y_330_, 2);
v___x_334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_inc(v_ref_333_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_ref_333_);
lean_ctor_set(v___x_339_, 1, v_a_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_327_ = stack[0].m_obj;
lean_object* v___y_328_ = stack[1].m_obj;
lean_object* v___y_329_ = stack[2].m_obj;
lean_object* v___y_330_ = stack[3].m_obj;
lean_object* v___y_331_ = stack[4].m_obj;
lean_object* v_res_344_;
v_res_344_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_361_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6));
v___x_362_ = lean_unsigned_to_nat(11u);
v___x_363_ = lean_unsigned_to_nat(129u);
v___x_364_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5));
v___x_365_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4));
v___x_366_ = l_mkPanicMessageWithDecl(v___x_365_, v___x_364_, v___x_363_, v___x_362_, v___x_361_);
return v___x_366_;
}
}
lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(lean_object* v_constName_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_381_; lean_object* v_env_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v___x_381_ = lean_st_ref_get(v___y_371_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_381_);
v___x_383_ = 0;
lean_inc(v_constName_367_);
v___x_384_ = l_Lean_Environment_findAsync_x3f(v_env_382_, v_constName_367_, v___x_383_);
if (lean_obj_tag(v___x_384_) == 1)
{
lean_object* v_val_385_; uint8_t v_kind_386_; 
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v___x_384_, 1);
v_kind_386_ = lean_ctor_get_uint8(v_val_385_, sizeof(void*)*3);
if (v_kind_386_ == 7)
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_385_);
if (lean_obj_tag(v___x_387_) == 7)
{
lean_object* v_val_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_constName_367_);
v_val_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_val_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set_tag(v___x_390_, 0);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_val_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v___x_387_);
v___x_396_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7);
v___x_397_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v___x_396_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
if (lean_obj_tag(v_a_398_) == 0)
{
lean_del_object(v___x_400_);
goto v___jp_373_;
}
else
{
lean_object* v_val_402_; lean_object* v___x_404_; 
lean_dec(v_constName_367_);
v_val_402_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v_a_398_, 1);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_val_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_val_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_constName_367_);
v_a_407_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_397_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_397_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_dec(v_val_385_);
goto v___jp_373_;
}
}
else
{
lean_dec(v___x_384_);
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_374_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_375_ = 0;
v___x_376_ = l_Lean_MessageData_ofConstName(v_constName_367_, v___x_375_);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3);
v___x_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_379_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_380_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_367_ = stack[0].m_obj;
lean_object* v___y_368_ = stack[1].m_obj;
lean_object* v___y_369_ = stack[2].m_obj;
lean_object* v___y_370_ = stack[3].m_obj;
lean_object* v___y_371_ = stack[4].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v_constName_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___boxed(lean_object* v_constName_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v_constName_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(lean_object* v_declName_423_, lean_object* v_majorPos_x3f_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___y_431_; lean_object* v___y_432_; 
if (lean_obj_tag(v_majorPos_x3f_424_) == 0)
{
lean_object* v___x_436_; lean_object* v_env_437_; uint8_t v___x_438_; 
v___x_436_ = lean_st_ref_get(v_a_428_);
v_env_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc_ref(v_env_437_);
lean_dec(v___x_436_);
lean_inc(v_declName_423_);
v___x_438_ = l_Lean_isAuxRecursor(v_env_437_, v_declName_423_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v_declName_423_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v_majorPos_x3f_424_);
return v___x_439_;
}
else
{
if (lean_obj_tag(v_declName_423_) == 1)
{
lean_object* v_pre_440_; lean_object* v_str_441_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_pre_440_ = lean_ctor_get(v_declName_423_, 0);
lean_inc(v_pre_440_);
v_str_441_ = lean_ctor_get(v_declName_423_, 1);
lean_inc_ref(v_str_441_);
lean_dec_ref_known(v_declName_423_, 2);
v___x_461_ = l_Lean_recOnSuffix;
v___x_462_ = lean_string_dec_eq(v_str_441_, v___x_461_);
if (v___x_462_ == 0)
{
if (v___x_438_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = l_Lean_casesOnSuffix;
v___x_464_ = lean_string_dec_eq(v_str_441_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = l_Lean_brecOnSuffix;
v___x_466_ = lean_string_dec_eq(v_str_441_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec_ref(v_str_441_);
lean_dec(v_pre_440_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_majorPos_x3f_424_);
return v___x_467_;
}
else
{
goto v___jp_442_;
}
}
else
{
goto v___jp_442_;
}
}
}
else
{
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_Lean_mkRecName(v_pre_440_);
v___x_444_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v___x_443_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_numParams_446_; lean_object* v_numIndices_447_; lean_object* v_numMotives_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v_numParams_446_ = lean_ctor_get(v_a_445_, 2);
lean_inc(v_numParams_446_);
v_numIndices_447_ = lean_ctor_get(v_a_445_, 3);
lean_inc(v_numIndices_447_);
v_numMotives_448_ = lean_ctor_get(v_a_445_, 4);
lean_inc(v_numMotives_448_);
lean_dec(v_a_445_);
v___x_449_ = lean_nat_add(v_numParams_446_, v_numIndices_447_);
lean_dec(v_numIndices_447_);
lean_dec(v_numParams_446_);
v___x_450_ = l_Lean_casesOnSuffix;
v___x_451_ = lean_string_dec_eq(v_str_441_, v___x_450_);
lean_dec_ref(v_str_441_);
if (v___x_451_ == 0)
{
v___y_431_ = v___x_449_;
v___y_432_ = v_numMotives_448_;
goto v___jp_430_;
}
else
{
lean_object* v___x_452_; 
lean_dec(v_numMotives_448_);
v___x_452_ = lean_unsigned_to_nat(1u);
v___y_431_ = v___x_449_;
v___y_432_ = v___x_452_;
goto v___jp_430_;
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec_ref(v_str_441_);
v_a_453_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_444_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_444_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_declName_423_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v_majorPos_x3f_424_);
return v___x_468_;
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v_declName_423_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_majorPos_x3f_424_);
return v___x_469_;
}
v___jp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_nat_add(v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec(v___y_431_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_423_ = stack[0].m_obj;
lean_object* v_majorPos_x3f_424_ = stack[1].m_obj;
lean_object* v_a_425_ = stack[2].m_obj;
lean_object* v_a_426_ = stack[3].m_obj;
lean_object* v_a_427_ = stack[4].m_obj;
lean_object* v_a_428_ = stack[5].m_obj;
lean_object* v_res_470_;
v_res_470_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_423_, v_majorPos_x3f_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___boxed(lean_object* v_declName_471_, lean_object* v_majorPos_x3f_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_471_, v_majorPos_x3f_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_478_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(lean_object* v_00_u03b1_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_480_ = stack[1].m_obj;
lean_object* v___y_481_ = stack[2].m_obj;
lean_object* v___y_482_ = stack[3].m_obj;
lean_object* v___y_483_ = stack[4].m_obj;
lean_object* v___y_484_ = stack[5].m_obj;
lean_object* v_res_487_;
v_res_487_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(lean_box(0), v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_488_, lean_object* v_msg_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(v_00_u03b1_488_, v_msg_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(uint8_t v___x_496_, lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_498_, v_stop_499_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_497_, v_i_498_);
v___x_506_ = l_Lean_Expr_isFVar(v___x_505_);
if (v___x_506_ == 0)
{
if (v___x_496_ == 0)
{
goto v___jp_500_;
}
else
{
return v___x_496_;
}
}
else
{
goto v___jp_500_;
}
}
else
{
uint8_t v___x_507_; 
v___x_507_ = 0;
return v___x_507_;
}
v___jp_500_:
{
size_t v___x_501_; size_t v___x_502_; 
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_498_, v___x_501_);
v_i_498_ = v___x_502_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_496_ = stack[0].m_num;
lean_object* v_as_497_ = stack[1].m_obj;
size_t v_i_498_ = stack[2].m_num;
size_t v_stop_499_ = stack[3].m_num;
uint8_t v_res_508_;
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_496_, v_as_497_, v_i_498_, v_stop_499_);
stack->m_num = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0___boxed(lean_object* v___x_509_, lean_object* v_as_510_, lean_object* v_i_511_, lean_object* v_stop_512_){
_start:
{
uint8_t v___x_476__boxed_513_; size_t v_i_boxed_514_; size_t v_stop_boxed_515_; uint8_t v_res_516_; lean_object* v_r_517_; 
v___x_476__boxed_513_ = lean_unbox(v___x_509_);
v_i_boxed_514_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_stop_boxed_515_ = lean_unbox_usize(v_stop_512_);
lean_dec(v_stop_512_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_476__boxed_513_, v_as_510_, v_i_boxed_514_, v_stop_boxed_515_);
lean_dec_ref(v_as_510_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0));
v___x_520_ = l_Lean_stringToMessageData(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2));
v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
return v___x_523_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(lean_object* v_declName_524_, lean_object* v_motive_525_, lean_object* v_motiveArgs_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
uint8_t v___y_536_; uint8_t v___y_544_; uint8_t v___x_545_; 
v___x_545_ = l_Lean_Expr_isFVar(v_motive_525_);
if (v___x_545_ == 0)
{
v___y_544_ = v___x_545_;
goto v___jp_543_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_array_get_size(v_motiveArgs_526_);
v___x_548_ = lean_nat_dec_lt(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
v___y_544_ = v___x_545_;
goto v___jp_543_;
}
else
{
if (v___x_548_ == 0)
{
v___y_544_ = v___x_545_;
goto v___jp_543_;
}
else
{
size_t v___x_549_; size_t v___x_550_; uint8_t v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_547_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_545_, v_motiveArgs_526_, v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v_declName_524_);
goto v___jp_532_;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = 0;
v___y_536_ = v___x_552_;
goto v___jp_535_;
}
}
}
}
v___jp_532_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_538_ = l_Lean_MessageData_ofConstName(v_declName_524_, v___y_536_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_541_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_542_;
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
v___y_536_ = v___y_544_;
goto v___jp_535_;
}
else
{
lean_dec(v_declName_524_);
goto v___jp_532_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_524_ = stack[0].m_obj;
lean_object* v_motive_525_ = stack[1].m_obj;
lean_object* v_motiveArgs_526_ = stack[2].m_obj;
lean_object* v_a_527_ = stack[3].m_obj;
lean_object* v_a_528_ = stack[4].m_obj;
lean_object* v_a_529_ = stack[5].m_obj;
lean_object* v_a_530_ = stack[6].m_obj;
lean_object* v_res_553_;
v_res_553_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_524_, v_motive_525_, v_motiveArgs_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(lean_object* v_declName_554_, lean_object* v_motive_555_, lean_object* v_motiveArgs_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_554_, v_motive_555_, v_motiveArgs_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec_ref(v_motiveArgs_556_);
lean_dec_ref(v_motive_555_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(lean_object* v_xs_563_, lean_object* v_motive_564_, lean_object* v_i_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v_xs_563_);
v___x_567_ = lean_nat_dec_lt(v_i_565_, v___x_566_);
if (v___x_567_ == 0)
{
return v_i_565_;
}
else
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_fget_borrowed(v_xs_563_, v_i_565_);
v___x_569_ = lean_expr_eqv(v_motive_564_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_i_565_, v___x_570_);
lean_dec(v_i_565_);
v_i_565_ = v___x_571_;
goto _start;
}
else
{
return v_i_565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(lean_object* v_xs_573_, lean_object* v_motive_574_, lean_object* v_i_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(v_xs_573_, v_motive_574_, v_i_575_);
lean_dec_ref(v_motive_574_);
lean_dec_ref(v_xs_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(lean_object* v_xs_577_, lean_object* v_v_578_, lean_object* v_i_579_){
_start:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_array_get_size(v_xs_577_);
v___x_581_ = lean_nat_dec_lt(v_i_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v_i_579_);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_fget_borrowed(v_xs_577_, v_i_579_);
v___x_584_ = lean_expr_eqv(v___x_583_, v_v_578_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v_i_579_, v___x_585_);
lean_dec(v_i_579_);
v_i_579_ = v___x_586_;
goto _start;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v_i_579_);
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_589_, lean_object* v_v_590_, lean_object* v_i_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_589_, v_v_590_, v_i_591_);
lean_dec_ref(v_v_590_);
lean_dec_ref(v_xs_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(lean_object* v_xs_593_, lean_object* v_v_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_593_, v_v_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0___boxed(lean_object* v_xs_597_, lean_object* v_v_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_597_, v_v_598_);
lean_dec_ref(v_v_598_);
lean_dec_ref(v_xs_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(lean_object* v_xs_600_, lean_object* v_v_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_600_, v_v_601_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(0);
return v___x_603_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_val_604_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_val_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0___boxed(lean_object* v_xs_612_, lean_object* v_v_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_612_, v_v_613_);
lean_dec_ref(v_v_613_);
lean_dec_ref(v_xs_612_);
return v_res_614_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(lean_object* v_a_615_, lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_eq(v_i_617_, v_stop_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_array_uget_borrowed(v_as_616_, v_i_617_);
v___x_621_ = lean_expr_eqv(v_a_615_, v___x_620_);
if (v___x_621_ == 0)
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_617_, v___x_622_);
v_i_617_ = v___x_623_;
goto _start;
}
else
{
return v___x_621_;
}
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_615_ = stack[0].m_obj;
lean_object* v_as_616_ = stack[1].m_obj;
size_t v_i_617_ = stack[2].m_num;
size_t v_stop_618_ = stack[3].m_num;
uint8_t v_res_626_;
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_615_, v_as_616_, v_i_617_, v_stop_618_);
stack->m_num = v_res_626_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2___boxed(lean_object* v_a_627_, lean_object* v_as_628_, lean_object* v_i_629_, lean_object* v_stop_630_){
_start:
{
size_t v_i_boxed_631_; size_t v_stop_boxed_632_; uint8_t v_res_633_; lean_object* v_r_634_; 
v_i_boxed_631_ = lean_unbox_usize(v_i_629_);
lean_dec(v_i_629_);
v_stop_boxed_632_ = lean_unbox_usize(v_stop_630_);
lean_dec(v_stop_630_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_627_, v_as_628_, v_i_boxed_631_, v_stop_boxed_632_);
lean_dec_ref(v_as_628_);
lean_dec_ref(v_a_627_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(lean_object* v_as_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_array_get_size(v_as_635_);
v___x_639_ = lean_nat_dec_lt(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
return v___x_639_;
}
else
{
if (v___x_639_ == 0)
{
return v___x_639_;
}
else
{
size_t v___x_640_; size_t v___x_641_; uint8_t v___x_642_; 
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_usize_of_nat(v___x_638_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_636_, v_as_635_, v___x_640_, v___x_641_);
return v___x_642_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_635_ = stack[0].m_obj;
lean_object* v_a_636_ = stack[1].m_obj;
uint8_t v_res_643_;
v_res_643_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_as_635_, v_a_636_);
stack->m_num = v_res_643_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1___boxed(lean_object* v_as_644_, lean_object* v_a_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_as_644_, v_a_645_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_as_644_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(lean_object* v_declName_663_, lean_object* v_majorPos_x3f_664_, lean_object* v_xs_665_, lean_object* v_motiveArgs_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
if (lean_obj_tag(v_majorPos_x3f_664_) == 0)
{
lean_object* v___x_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_672_ = l_Lean_instInhabitedExpr;
v___x_702_ = lean_array_get_size(v_motiveArgs_666_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
v___y_674_ = v_a_667_;
v___y_675_ = v_a_668_;
v___y_676_ = v_a_669_;
v___y_677_ = v_a_670_;
goto v___jp_673_;
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3);
v___x_706_ = 0;
v___x_707_ = l_Lean_MessageData_ofConstName(v_declName_663_, v___x_706_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_705_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_710_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
v___jp_673_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_major_681_; lean_object* v___x_682_; 
v___x_678_ = lean_array_get_size(v_motiveArgs_666_);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_sub(v___x_678_, v___x_679_);
v_major_681_ = lean_array_get_borrowed(v___x_672_, v_motiveArgs_666_, v___x_680_);
lean_dec(v___x_680_);
v___x_682_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_665_, v_major_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1);
v___x_684_ = 0;
v___x_685_ = l_Lean_MessageData_ofConstName(v_declName_663_, v___x_684_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_688_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v___x_689_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_declName_663_);
v_val_690_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_701_ == 0)
{
v___x_692_ = v___x_682_;
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v___x_682_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_694_ = 1;
v___x_695_ = lean_box(v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_val_690_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
lean_inc(v_major_681_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_major_681_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 0);
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
else
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_declName_663_);
v_val_720_ = lean_ctor_get(v_majorPos_x3f_664_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_majorPos_x3f_664_);
if (v_isSharedCheck_744_ == 0)
{
v___x_722_ = v_majorPos_x3f_664_;
v_isShared_723_ = v_isSharedCheck_744_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v_majorPos_x3f_664_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_744_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_array_get_size(v_xs_665_);
v___x_725_ = lean_nat_dec_lt(v_val_720_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
lean_dec(v_val_720_);
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7);
v___x_727_ = l_Nat_reprFast(v___x_724_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 3);
lean_ctor_set(v___x_722_, 0, v___x_727_);
v___x_729_ = v___x_722_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_735_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_730_ = l_Lean_MessageData_ofFormat(v___x_729_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_726_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_733_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
return v___x_734_;
}
}
else
{
lean_object* v_major_736_; uint8_t v_depElim_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v_major_736_ = lean_array_fget_borrowed(v_xs_665_, v_val_720_);
v_depElim_737_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_motiveArgs_666_, v_major_736_);
v___x_738_ = lean_box(v_depElim_737_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_val_720_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_inc(v_major_736_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_major_736_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
lean_ctor_set(v___x_722_, 0, v___x_740_);
v___x_742_ = v___x_722_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_663_ = stack[0].m_obj;
lean_object* v_majorPos_x3f_664_ = stack[1].m_obj;
lean_object* v_xs_665_ = stack[2].m_obj;
lean_object* v_motiveArgs_666_ = stack[3].m_obj;
lean_object* v_a_667_ = stack[4].m_obj;
lean_object* v_a_668_ = stack[5].m_obj;
lean_object* v_a_669_ = stack[6].m_obj;
lean_object* v_a_670_ = stack[7].m_obj;
lean_object* v_res_745_;
v_res_745_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_663_, v_majorPos_x3f_664_, v_xs_665_, v_motiveArgs_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(lean_object* v_declName_746_, lean_object* v_majorPos_x3f_747_, lean_object* v_xs_748_, lean_object* v_motiveArgs_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_746_, v_majorPos_x3f_747_, v_xs_748_, v_motiveArgs_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_motiveArgs_749_);
lean_dec_ref(v_xs_748_);
return v_res_755_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(lean_object* v___x_756_, lean_object* v_as_757_, size_t v_sz_758_, size_t v_i_759_, lean_object* v_b_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_lt(v_i_759_, v_sz_758_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v___x_756_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_b_760_);
return v___x_767_;
}
else
{
lean_object* v_snd_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_805_; 
v_snd_768_ = lean_ctor_get(v_b_760_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_b_760_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v_b_760_, 0);
lean_dec(v_unused_806_);
v___x_770_ = v_b_760_;
v_isShared_771_ = v_isSharedCheck_805_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snd_768_);
lean_dec(v_b_760_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_805_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v_a_773_; lean_object* v___x_774_; 
v___x_772_ = lean_box(0);
v_a_773_ = lean_array_uget_borrowed(v_as_757_, v_i_759_);
lean_inc_ref(v___x_756_);
lean_inc(v_a_773_);
v___x_774_ = l_Lean_Meta_isExprDefEq(v_a_773_, v___x_756_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_796_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_796_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_796_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_796_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
uint8_t v___x_779_; 
v___x_779_ = lean_unbox(v_a_775_);
lean_dec(v_a_775_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_del_object(v___x_777_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_snd_768_, v___x_780_);
lean_dec(v_snd_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_781_);
lean_ctor_set(v___x_770_, 0, v___x_772_);
v___x_783_ = v___x_770_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
size_t v___x_784_; size_t v___x_785_; 
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_759_, v___x_784_);
v_i_759_ = v___x_785_;
v_b_760_ = v___x_783_;
goto _start;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
lean_dec_ref(v___x_756_);
lean_inc(v_snd_768_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_snd_768_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_789_);
v___x_791_ = v___x_770_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_768_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_791_);
v___x_793_ = v___x_777_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_del_object(v___x_770_);
lean_dec(v_snd_768_);
lean_dec_ref(v___x_756_);
v_a_797_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_774_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_774_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_756_ = stack[0].m_obj;
lean_object* v_as_757_ = stack[1].m_obj;
size_t v_sz_758_ = stack[2].m_num;
size_t v_i_759_ = stack[3].m_num;
lean_object* v_b_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v___y_762_ = stack[6].m_obj;
lean_object* v___y_763_ = stack[7].m_obj;
lean_object* v___y_764_ = stack[8].m_obj;
lean_object* v_res_807_;
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_756_, v_as_757_, v_sz_758_, v_i_759_, v_b_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0___boxed(lean_object* v___x_808_, lean_object* v_as_809_, lean_object* v_sz_810_, lean_object* v_i_811_, lean_object* v_b_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
size_t v_sz_boxed_818_; size_t v_i_boxed_819_; lean_object* v_res_820_; 
v_sz_boxed_818_ = lean_unbox_usize(v_sz_810_);
lean_dec(v_sz_810_);
v_i_boxed_819_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_808_, v_as_809_, v_sz_boxed_818_, v_i_boxed_819_, v_b_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_as_809_);
return v_res_820_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(lean_object* v_upperBound_827_, lean_object* v_xs_828_, lean_object* v_declName_829_, lean_object* v_Iargs_830_, lean_object* v_a_831_, lean_object* v_b_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_a_839_; uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_lt(v_a_831_, v_upperBound_827_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v_a_831_);
lean_dec(v_declName_829_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_832_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_a_848_; lean_object* v___x_877_; lean_object* v___x_878_; size_t v_sz_879_; size_t v___x_880_; lean_object* v___x_881_; 
v___x_845_ = l_Lean_instInhabitedExpr;
v___x_846_ = lean_array_get_borrowed(v___x_845_, v_xs_828_, v_a_831_);
v___x_877_ = lean_box(0);
v___x_878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2));
v_sz_879_ = lean_array_size(v_Iargs_830_);
v___x_880_ = ((size_t)0ULL);
lean_inc(v___x_846_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_846_, v_Iargs_830_, v_sz_879_, v___x_880_, v___x_878_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_fst_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v_fst_883_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_fst_883_);
lean_dec(v_a_882_);
if (lean_obj_tag(v_fst_883_) == 0)
{
v_a_848_ = v___x_877_;
goto v___jp_847_;
}
else
{
lean_object* v_val_884_; 
v_val_884_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_fst_883_, 1);
if (lean_obj_tag(v_val_884_) == 0)
{
v_a_848_ = v_val_884_;
goto v___jp_847_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = lean_array_push(v_b_832_, v_val_884_);
v_a_839_ = v___x_885_;
goto v___jp_838_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_b_832_);
lean_dec(v_a_831_);
lean_dec(v_declName_829_);
v_a_886_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_881_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_881_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
v___jp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Lean_Expr_fvarId_x21(v___x_846_);
v___x_850_ = l_Lean_FVarId_getDecl___redArg(v___x_849_, v___y_833_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; uint8_t v___x_852_; uint8_t v___x_853_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = l_Lean_LocalDecl_binderInfo(v_a_851_);
lean_dec(v_a_851_);
v___x_853_ = l_Lean_BinderInfo_isInstImplicit(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_a_848_);
v___x_854_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
lean_inc(v_declName_829_);
v___x_855_ = l_Lean_MessageData_ofConstName(v_declName_829_, v___x_853_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_858_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_dec_ref_known(v___x_859_, 1);
v_a_839_ = v_b_832_;
goto v___jp_838_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v_b_832_);
lean_dec(v_a_831_);
lean_dec(v_declName_829_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v___x_868_; 
v___x_868_ = lean_array_push(v_b_832_, v_a_848_);
v_a_839_ = v___x_868_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_a_848_);
lean_dec_ref(v_b_832_);
lean_dec(v_a_831_);
lean_dec(v_declName_829_);
v_a_869_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_850_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_850_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_a_831_, v___x_840_);
lean_dec(v_a_831_);
v_a_831_ = v___x_841_;
v_b_832_ = v_a_839_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_827_ = stack[0].m_obj;
lean_object* v_xs_828_ = stack[1].m_obj;
lean_object* v_declName_829_ = stack[2].m_obj;
lean_object* v_Iargs_830_ = stack[3].m_obj;
lean_object* v_a_831_ = stack[4].m_obj;
lean_object* v_b_832_ = stack[5].m_obj;
lean_object* v___y_833_ = stack[6].m_obj;
lean_object* v___y_834_ = stack[7].m_obj;
lean_object* v___y_835_ = stack[8].m_obj;
lean_object* v___y_836_ = stack[9].m_obj;
lean_object* v_res_894_;
v_res_894_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_827_, v_xs_828_, v_declName_829_, v_Iargs_830_, v_a_831_, v_b_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___boxed(lean_object* v_upperBound_895_, lean_object* v_xs_896_, lean_object* v_declName_897_, lean_object* v_Iargs_898_, lean_object* v_a_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_895_, v_xs_896_, v_declName_897_, v_Iargs_898_, v_a_899_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec_ref(v_Iargs_898_);
lean_dec_ref(v_xs_896_);
lean_dec(v_upperBound_895_);
return v_res_906_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(lean_object* v_declName_909_, lean_object* v_xs_910_, lean_object* v_numParams_911_, lean_object* v_Iargs_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_paramsPos_919_; lean_object* v___x_920_; 
v___x_918_ = lean_unsigned_to_nat(0u);
v_paramsPos_919_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0));
v___x_920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_numParams_911_, v_xs_910_, v_declName_909_, v_Iargs_912_, v___x_918_, v_paramsPos_919_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_929_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_929_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_array_to_list(v_a_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_a_930_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_920_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_920_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_909_ = stack[0].m_obj;
lean_object* v_xs_910_ = stack[1].m_obj;
lean_object* v_numParams_911_ = stack[2].m_obj;
lean_object* v_Iargs_912_ = stack[3].m_obj;
lean_object* v_a_913_ = stack[4].m_obj;
lean_object* v_a_914_ = stack[5].m_obj;
lean_object* v_a_915_ = stack[6].m_obj;
lean_object* v_a_916_ = stack[7].m_obj;
lean_object* v_res_938_;
v_res_938_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_909_, v_xs_910_, v_numParams_911_, v_Iargs_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(lean_object* v_declName_939_, lean_object* v_xs_940_, lean_object* v_numParams_941_, lean_object* v_Iargs_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_939_, v_xs_940_, v_numParams_941_, v_Iargs_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_Iargs_942_);
lean_dec(v_numParams_941_);
lean_dec_ref(v_xs_940_);
return v_res_948_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(lean_object* v_upperBound_949_, lean_object* v_xs_950_, lean_object* v_declName_951_, lean_object* v_Iargs_952_, lean_object* v_inst_953_, lean_object* v_R_954_, lean_object* v_a_955_, lean_object* v_b_956_, lean_object* v_c_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_949_, v_xs_950_, v_declName_951_, v_Iargs_952_, v_a_955_, v_b_956_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_963_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_949_ = stack[0].m_obj;
lean_object* v_xs_950_ = stack[1].m_obj;
lean_object* v_declName_951_ = stack[2].m_obj;
lean_object* v_Iargs_952_ = stack[3].m_obj;
lean_object* v_a_955_ = stack[6].m_obj;
lean_object* v_b_956_ = stack[7].m_obj;
lean_object* v___y_958_ = stack[9].m_obj;
lean_object* v___y_959_ = stack[10].m_obj;
lean_object* v___y_960_ = stack[11].m_obj;
lean_object* v___y_961_ = stack[12].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(v_upperBound_949_, v_xs_950_, v_declName_951_, v_Iargs_952_, lean_box(0), lean_box(0), v_a_955_, v_b_956_, lean_box(0), v___y_958_, v___y_959_, v___y_960_, v___y_961_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___boxed(lean_object* v_upperBound_965_, lean_object* v_xs_966_, lean_object* v_declName_967_, lean_object* v_Iargs_968_, lean_object* v_inst_969_, lean_object* v_R_970_, lean_object* v_a_971_, lean_object* v_b_972_, lean_object* v_c_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(v_upperBound_965_, v_xs_966_, v_declName_967_, v_Iargs_968_, v_inst_969_, v_R_970_, v_a_971_, v_b_972_, v_c_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_Iargs_968_);
lean_dec_ref(v_xs_966_);
lean_dec(v_upperBound_965_);
return v_res_979_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(lean_object* v_declName_983_, lean_object* v_upperBound_984_, lean_object* v_majorPos_985_, lean_object* v_numIndices_986_, lean_object* v_xs_987_, lean_object* v_Iargs_988_, lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_a_997_; uint8_t v___x_1017_; 
v___x_1017_ = lean_nat_dec_lt(v_a_989_, v_upperBound_984_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_a_989_);
lean_dec(v_declName_983_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_990_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; size_t v_sz_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1019_ = l_Lean_instInhabitedExpr;
v___x_1020_ = lean_nat_sub(v_majorPos_985_, v_numIndices_986_);
v___x_1021_ = lean_nat_add(v___x_1020_, v_a_989_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_array_get_borrowed(v___x_1019_, v_xs_987_, v___x_1021_);
lean_dec(v___x_1021_);
v___x_1023_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2));
v_sz_1024_ = lean_array_size(v_Iargs_988_);
v___x_1025_ = ((size_t)0ULL);
lean_inc(v___x_1022_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_1022_, v_Iargs_988_, v_sz_1024_, v___x_1025_, v___x_1023_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v_fst_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v_fst_1028_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_fst_1028_);
lean_dec(v_a_1027_);
if (lean_obj_tag(v_fst_1028_) == 0)
{
goto v___jp_1001_;
}
else
{
lean_object* v_val_1029_; 
v_val_1029_ = lean_ctor_get(v_fst_1028_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_fst_1028_, 1);
if (lean_obj_tag(v_val_1029_) == 0)
{
goto v___jp_1001_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
v_val_1030_ = lean_ctor_get(v_val_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v_val_1029_, 1);
v___x_1031_ = lean_array_push(v_b_990_, v_val_1030_);
v_a_997_ = v___x_1031_;
goto v___jp_996_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_b_990_);
lean_dec(v_a_989_);
lean_dec(v_declName_983_);
v_a_1032_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1026_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1026_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_nat_add(v_a_989_, v___x_998_);
lean_dec(v_a_989_);
v_a_989_ = v___x_999_;
v_b_990_ = v_a_997_;
goto _start;
}
v___jp_1001_:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1003_ = 0;
lean_inc(v_declName_983_);
v___x_1004_ = l_Lean_MessageData_ofConstName(v_declName_983_, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1007_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_dec_ref_known(v___x_1008_, 1);
v_a_997_ = v_b_990_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_b_990_);
lean_dec(v_a_989_);
lean_dec(v_declName_983_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_983_ = stack[0].m_obj;
lean_object* v_upperBound_984_ = stack[1].m_obj;
lean_object* v_majorPos_985_ = stack[2].m_obj;
lean_object* v_numIndices_986_ = stack[3].m_obj;
lean_object* v_xs_987_ = stack[4].m_obj;
lean_object* v_Iargs_988_ = stack[5].m_obj;
lean_object* v_a_989_ = stack[6].m_obj;
lean_object* v_b_990_ = stack[7].m_obj;
lean_object* v___y_991_ = stack[8].m_obj;
lean_object* v___y_992_ = stack[9].m_obj;
lean_object* v___y_993_ = stack[10].m_obj;
lean_object* v___y_994_ = stack[11].m_obj;
lean_object* v_res_1040_;
v_res_1040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_983_, v_upperBound_984_, v_majorPos_985_, v_numIndices_986_, v_xs_987_, v_Iargs_988_, v_a_989_, v_b_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___boxed(lean_object* v_declName_1041_, lean_object* v_upperBound_1042_, lean_object* v_majorPos_1043_, lean_object* v_numIndices_1044_, lean_object* v_xs_1045_, lean_object* v_Iargs_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1041_, v_upperBound_1042_, v_majorPos_1043_, v_numIndices_1044_, v_xs_1045_, v_Iargs_1046_, v_a_1047_, v_b_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v_Iargs_1046_);
lean_dec_ref(v_xs_1045_);
lean_dec(v_numIndices_1044_);
lean_dec(v_majorPos_1043_);
lean_dec(v_upperBound_1042_);
return v_res_1054_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(lean_object* v_declName_1057_, lean_object* v_xs_1058_, lean_object* v_majorPos_1059_, lean_object* v_numIndices_1060_, lean_object* v_Iargs_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v_indicesPos_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v_indicesPos_1068_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0));
v___x_1069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1057_, v_numIndices_1060_, v_majorPos_1059_, v_numIndices_1060_, v_xs_1058_, v_Iargs_1061_, v___x_1067_, v_indicesPos_1068_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_array_to_list(v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1069_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1069_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1057_ = stack[0].m_obj;
lean_object* v_xs_1058_ = stack[1].m_obj;
lean_object* v_majorPos_1059_ = stack[2].m_obj;
lean_object* v_numIndices_1060_ = stack[3].m_obj;
lean_object* v_Iargs_1061_ = stack[4].m_obj;
lean_object* v_a_1062_ = stack[5].m_obj;
lean_object* v_a_1063_ = stack[6].m_obj;
lean_object* v_a_1064_ = stack[7].m_obj;
lean_object* v_a_1065_ = stack[8].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1057_, v_xs_1058_, v_majorPos_1059_, v_numIndices_1060_, v_Iargs_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(lean_object* v_declName_1088_, lean_object* v_xs_1089_, lean_object* v_majorPos_1090_, lean_object* v_numIndices_1091_, lean_object* v_Iargs_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1088_, v_xs_1089_, v_majorPos_1090_, v_numIndices_1091_, v_Iargs_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec_ref(v_Iargs_1092_);
lean_dec(v_numIndices_1091_);
lean_dec(v_majorPos_1090_);
lean_dec_ref(v_xs_1089_);
return v_res_1098_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(lean_object* v_declName_1099_, lean_object* v_upperBound_1100_, lean_object* v_majorPos_1101_, lean_object* v_numIndices_1102_, lean_object* v_xs_1103_, lean_object* v_Iargs_1104_, lean_object* v_inst_1105_, lean_object* v_R_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_, lean_object* v_c_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1099_, v_upperBound_1100_, v_majorPos_1101_, v_numIndices_1102_, v_xs_1103_, v_Iargs_1104_, v_a_1107_, v_b_1108_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1099_ = stack[0].m_obj;
lean_object* v_upperBound_1100_ = stack[1].m_obj;
lean_object* v_majorPos_1101_ = stack[2].m_obj;
lean_object* v_numIndices_1102_ = stack[3].m_obj;
lean_object* v_xs_1103_ = stack[4].m_obj;
lean_object* v_Iargs_1104_ = stack[5].m_obj;
lean_object* v_a_1107_ = stack[8].m_obj;
lean_object* v_b_1108_ = stack[9].m_obj;
lean_object* v___y_1110_ = stack[11].m_obj;
lean_object* v___y_1111_ = stack[12].m_obj;
lean_object* v___y_1112_ = stack[13].m_obj;
lean_object* v___y_1113_ = stack[14].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(v_declName_1099_, v_upperBound_1100_, v_majorPos_1101_, v_numIndices_1102_, v_xs_1103_, v_Iargs_1104_, lean_box(0), lean_box(0), v_a_1107_, v_b_1108_, lean_box(0), v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___boxed(lean_object* v_declName_1117_, lean_object* v_upperBound_1118_, lean_object* v_majorPos_1119_, lean_object* v_numIndices_1120_, lean_object* v_xs_1121_, lean_object* v_Iargs_1122_, lean_object* v_inst_1123_, lean_object* v_R_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_c_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(v_declName_1117_, v_upperBound_1118_, v_majorPos_1119_, v_numIndices_1120_, v_xs_1121_, v_Iargs_1122_, v_inst_1123_, v_R_1124_, v_a_1125_, v_b_1126_, v_c_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_Iargs_1122_);
lean_dec_ref(v_xs_1121_);
lean_dec(v_numIndices_1120_);
lean_dec(v_majorPos_1119_);
lean_dec(v_upperBound_1118_);
return v_res_1133_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(lean_object* v_declName_1137_, lean_object* v_motiveResultType_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; 
if (lean_obj_tag(v_motiveResultType_1138_) == 3)
{
lean_object* v_u_1156_; 
v_u_1156_ = lean_ctor_get(v_motiveResultType_1138_, 0);
switch(lean_obj_tag(v_u_1156_))
{
case 0:
{
lean_object* v___x_1157_; 
lean_dec(v_declName_1137_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_u_1156_);
return v___x_1157_;
}
case 4:
{
lean_object* v___x_1158_; 
lean_dec(v_declName_1137_);
lean_inc_ref(v_u_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_u_1156_);
return v___x_1158_;
}
default: 
{
v___y_1145_ = v_a_1139_;
v___y_1146_ = v_a_1140_;
v___y_1147_ = v_a_1141_;
v___y_1148_ = v_a_1142_;
goto v___jp_1144_;
}
}
}
else
{
v___y_1145_ = v_a_1139_;
v___y_1146_ = v_a_1140_;
v___y_1147_ = v_a_1141_;
v___y_1148_ = v_a_1142_;
goto v___jp_1144_;
}
v___jp_1144_:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1150_ = 0;
v___x_1151_ = l_Lean_MessageData_ofConstName(v_declName_1137_, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1149_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1154_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1155_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1137_ = stack[0].m_obj;
lean_object* v_motiveResultType_1138_ = stack[1].m_obj;
lean_object* v_a_1139_ = stack[2].m_obj;
lean_object* v_a_1140_ = stack[3].m_obj;
lean_object* v_a_1141_ = stack[4].m_obj;
lean_object* v_a_1142_ = stack[5].m_obj;
lean_object* v_res_1159_;
v_res_1159_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1137_, v_motiveResultType_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(lean_object* v_declName_1160_, lean_object* v_motiveResultType_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1160_, v_motiveResultType_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec_ref(v_motiveResultType_1161_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(lean_object* v___x_1168_, lean_object* v_as_1169_, lean_object* v_j_1170_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_array_get_size(v_as_1169_);
v___x_1172_ = lean_nat_dec_lt(v_j_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec(v_j_1170_);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_array_fget_borrowed(v_as_1169_, v_j_1170_);
v___x_1175_ = lean_level_eq(v___x_1174_, v___x_1168_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_add(v_j_1170_, v___x_1176_);
lean_dec(v_j_1170_);
v_j_1170_ = v___x_1177_;
goto _start;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_j_1170_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0___boxed(lean_object* v___x_1180_, lean_object* v_as_1181_, lean_object* v_j_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_1180_, v_as_1181_, v_j_1182_);
lean_dec_ref(v_as_1181_);
lean_dec(v___x_1180_);
return v_res_1183_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(lean_object* v_motiveLvl_1187_, lean_object* v_Ilevels_1188_, lean_object* v_declName_1189_, lean_object* v_as_x27_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
if (lean_obj_tag(v_as_x27_1190_) == 0)
{
lean_object* v___x_1197_; 
lean_dec(v_declName_1189_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_b_1191_);
return v___x_1197_;
}
else
{
lean_object* v_head_1198_; lean_object* v_tail_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_head_1198_ = lean_ctor_get(v_as_x27_1190_, 0);
v_tail_1199_ = lean_ctor_get(v_as_x27_1190_, 1);
lean_inc(v_head_1198_);
v___x_1200_ = l_Lean_mkLevelParam(v_head_1198_);
v___x_1201_ = lean_level_eq(v_motiveLvl_1187_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_1200_, v_Ilevels_1188_, v___x_1202_);
lean_dec(v___x_1200_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_b_1191_);
v___x_1204_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1205_ = l_Lean_MessageData_ofConstName(v_declName_1189_, v___x_1201_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_inc(v_head_1198_);
v___x_1209_ = l_Lean_MessageData_ofName(v_head_1198_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1212_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1231_; 
v_val_1222_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1224_ = v___x_1203_;
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_val_1222_);
lean_dec(v___x_1203_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_val_1222_);
v___x_1227_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_array_push(v_b_1191_, v___x_1227_);
v_as_x27_1190_ = v_tail_1199_;
v_b_1191_ = v___x_1228_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v___x_1200_);
v___x_1232_ = lean_box(0);
v___x_1233_ = lean_array_push(v_b_1191_, v___x_1232_);
v_as_x27_1190_ = v_tail_1199_;
v_b_1191_ = v___x_1233_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_motiveLvl_1187_ = stack[0].m_obj;
lean_object* v_Ilevels_1188_ = stack[1].m_obj;
lean_object* v_declName_1189_ = stack[2].m_obj;
lean_object* v_as_x27_1190_ = stack[3].m_obj;
lean_object* v_b_1191_ = stack[4].m_obj;
lean_object* v___y_1192_ = stack[5].m_obj;
lean_object* v___y_1193_ = stack[6].m_obj;
lean_object* v___y_1194_ = stack[7].m_obj;
lean_object* v___y_1195_ = stack[8].m_obj;
lean_object* v_res_1235_;
v_res_1235_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1187_, v_Ilevels_1188_, v_declName_1189_, v_as_x27_1190_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
stack->m_obj
 = v_res_1235_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___boxed(lean_object* v_motiveLvl_1236_, lean_object* v_Ilevels_1237_, lean_object* v_declName_1238_, lean_object* v_as_x27_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1236_, v_Ilevels_1237_, v_declName_1238_, v_as_x27_1239_, v_b_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v_as_x27_1239_);
lean_dec_ref(v_Ilevels_1237_);
lean_dec(v_motiveLvl_1236_);
return v_res_1246_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(lean_object* v_declName_1249_, lean_object* v_lparams_1250_, lean_object* v_motiveLvl_1251_, lean_object* v_Ilevels_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_Ilevels_1258_; lean_object* v_univLevelPos_1259_; lean_object* v___x_1260_; 
v_Ilevels_1258_ = lean_array_mk(v_Ilevels_1252_);
v_univLevelPos_1259_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0));
v___x_1260_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1251_, v_Ilevels_1258_, v_declName_1249_, v_lparams_1250_, v_univLevelPos_1259_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec_ref(v_Ilevels_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_array_to_list(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1260_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1260_);
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
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1249_ = stack[0].m_obj;
lean_object* v_lparams_1250_ = stack[1].m_obj;
lean_object* v_motiveLvl_1251_ = stack[2].m_obj;
lean_object* v_Ilevels_1252_ = stack[3].m_obj;
lean_object* v_a_1253_ = stack[4].m_obj;
lean_object* v_a_1254_ = stack[5].m_obj;
lean_object* v_a_1255_ = stack[6].m_obj;
lean_object* v_a_1256_ = stack[7].m_obj;
lean_object* v_res_1278_;
v_res_1278_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1249_, v_lparams_1250_, v_motiveLvl_1251_, v_Ilevels_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(lean_object* v_declName_1279_, lean_object* v_lparams_1280_, lean_object* v_motiveLvl_1281_, lean_object* v_Ilevels_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1279_, v_lparams_1280_, v_motiveLvl_1281_, v_Ilevels_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_motiveLvl_1281_);
lean_dec(v_lparams_1280_);
return v_res_1288_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(lean_object* v_motiveLvl_1289_, lean_object* v_Ilevels_1290_, lean_object* v_declName_1291_, lean_object* v_as_1292_, lean_object* v_as_x27_1293_, lean_object* v_b_1294_, lean_object* v_a_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1289_, v_Ilevels_1290_, v_declName_1291_, v_as_x27_1293_, v_b_1294_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_motiveLvl_1289_ = stack[0].m_obj;
lean_object* v_Ilevels_1290_ = stack[1].m_obj;
lean_object* v_declName_1291_ = stack[2].m_obj;
lean_object* v_as_1292_ = stack[3].m_obj;
lean_object* v_as_x27_1293_ = stack[4].m_obj;
lean_object* v_b_1294_ = stack[5].m_obj;
lean_object* v___y_1296_ = stack[7].m_obj;
lean_object* v___y_1297_ = stack[8].m_obj;
lean_object* v___y_1298_ = stack[9].m_obj;
lean_object* v___y_1299_ = stack[10].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(v_motiveLvl_1289_, v_Ilevels_1290_, v_declName_1291_, v_as_1292_, v_as_x27_1293_, v_b_1294_, lean_box(0), v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___boxed(lean_object* v_motiveLvl_1303_, lean_object* v_Ilevels_1304_, lean_object* v_declName_1305_, lean_object* v_as_1306_, lean_object* v_as_x27_1307_, lean_object* v_b_1308_, lean_object* v_a_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(v_motiveLvl_1303_, v_Ilevels_1304_, v_declName_1305_, v_as_1306_, v_as_x27_1307_, v_b_1308_, v_a_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_as_x27_1307_);
lean_dec(v_as_1306_);
lean_dec_ref(v_Ilevels_1304_);
lean_dec(v_motiveLvl_1303_);
return v_res_1315_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(lean_object* v_k_1316_, lean_object* v_b_1317_, lean_object* v_c_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; 
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1324_ = lean_apply_7(v_k_1316_, v_b_1317_, v_c_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, lean_box(0));
return v___x_1324_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1316_ = stack[0].m_obj;
lean_object* v_b_1317_ = stack[1].m_obj;
lean_object* v_c_1318_ = stack[2].m_obj;
lean_object* v___y_1319_ = stack[3].m_obj;
lean_object* v___y_1320_ = stack[4].m_obj;
lean_object* v___y_1321_ = stack[5].m_obj;
lean_object* v___y_1322_ = stack[6].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(v_k_1316_, v_b_1317_, v_c_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
stack->m_obj
 = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed(lean_object* v_k_1326_, lean_object* v_b_1327_, lean_object* v_c_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(v_k_1326_, v_b_1327_, v_c_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1334_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(lean_object* v_type_1335_, lean_object* v_k_1336_, uint8_t v_cleanupAnnotations_1337_, uint8_t v_whnfType_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___f_1344_; lean_object* v___x_1345_; 
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1344_, 0, v_k_1336_);
v___x_1345_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1335_, v___f_1344_, v_cleanupAnnotations_1337_, v_whnfType_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1345_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1345_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
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
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1335_ = stack[0].m_obj;
lean_object* v_k_1336_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1337_ = stack[2].m_num;
uint8_t v_whnfType_1338_ = stack[3].m_num;
lean_object* v___y_1339_ = stack[4].m_obj;
lean_object* v___y_1340_ = stack[5].m_obj;
lean_object* v___y_1341_ = stack[6].m_obj;
lean_object* v___y_1342_ = stack[7].m_obj;
lean_object* v_res_1362_;
v_res_1362_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1335_, v_k_1336_, v_cleanupAnnotations_1337_, v_whnfType_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
stack->m_obj
 = v_res_1362_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___boxed(lean_object* v_type_1363_, lean_object* v_k_1364_, lean_object* v_cleanupAnnotations_1365_, lean_object* v_whnfType_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1372_; uint8_t v_whnfType_boxed_1373_; lean_object* v_res_1374_; 
v_cleanupAnnotations_boxed_1372_ = lean_unbox(v_cleanupAnnotations_1365_);
v_whnfType_boxed_1373_ = lean_unbox(v_whnfType_1366_);
v_res_1374_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1363_, v_k_1364_, v_cleanupAnnotations_boxed_1372_, v_whnfType_boxed_1373_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1374_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(lean_object* v_00_u03b1_1375_, lean_object* v_type_1376_, lean_object* v_k_1377_, uint8_t v_cleanupAnnotations_1378_, uint8_t v_whnfType_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1376_, v_k_1377_, v_cleanupAnnotations_1378_, v_whnfType_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1376_ = stack[1].m_obj;
lean_object* v_k_1377_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1378_ = stack[3].m_num;
uint8_t v_whnfType_1379_ = stack[4].m_num;
lean_object* v___y_1380_ = stack[5].m_obj;
lean_object* v___y_1381_ = stack[6].m_obj;
lean_object* v___y_1382_ = stack[7].m_obj;
lean_object* v___y_1383_ = stack[8].m_obj;
lean_object* v_res_1386_;
v_res_1386_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(lean_box(0), v_type_1376_, v_k_1377_, v_cleanupAnnotations_1378_, v_whnfType_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
stack->m_obj
 = v_res_1386_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___boxed(lean_object* v_00_u03b1_1387_, lean_object* v_type_1388_, lean_object* v_k_1389_, lean_object* v_cleanupAnnotations_1390_, lean_object* v_whnfType_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1397_; uint8_t v_whnfType_boxed_1398_; lean_object* v_res_1399_; 
v_cleanupAnnotations_boxed_1397_ = lean_unbox(v_cleanupAnnotations_1390_);
v_whnfType_boxed_1398_ = lean_unbox(v_whnfType_1391_);
v_res_1399_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(v_00_u03b1_1387_, v_type_1388_, v_k_1389_, v_cleanupAnnotations_boxed_1397_, v_whnfType_boxed_1398_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1399_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(lean_object* v_motive_1400_, lean_object* v_e_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_expr_eqv(v_e_1401_, v_motive_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_1400_ = stack[0].m_obj;
lean_object* v_e_1401_ = stack[1].m_obj;
uint8_t v_res_1403_;
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(v_motive_1400_, v_e_1401_);
stack->m_num = v_res_1403_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed(lean_object* v_motive_1404_, lean_object* v_e_1405_){
_start:
{
uint8_t v_res_1406_; lean_object* v_r_1407_; 
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(v_motive_1404_, v_e_1405_);
lean_dec_ref(v_e_1405_);
lean_dec_ref(v_motive_1404_);
v_r_1407_ = lean_box(v_res_1406_);
return v_r_1407_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(lean_object* v_motive_1408_, uint8_t v___x_1409_, lean_object* v_next_1410_, lean_object* v_upperBound_1411_, lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1420_ == 0)
{
lean_object* v___f_1421_; uint8_t v___x_1422_; uint8_t v___x_1423_; uint8_t v_a_1425_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_inc_ref(v_motive_1408_);
v___f_1421_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1421_, 0, v_motive_1408_);
v___x_1422_ = lean_nat_dec_lt(v_next_1410_, v_upperBound_1411_);
v___x_1423_ = 1;
v___x_1431_ = lean_array_uget_borrowed(v_as_1412_, v_i_1413_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
lean_inc(v___x_1431_);
v___x_1432_ = lean_infer_type(v___x_1431_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = lean_find_expr(v___f_1421_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec_ref(v___f_1421_);
if (lean_obj_tag(v___x_1434_) == 0)
{
v_a_1425_ = v___x_1409_;
goto v___jp_1424_;
}
else
{
lean_dec_ref_known(v___x_1434_, 1);
v_a_1425_ = v___x_1422_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v___f_1421_);
lean_dec_ref(v_motive_1408_);
v_a_1435_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1432_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1432_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
v___jp_1424_:
{
if (v_a_1425_ == 0)
{
size_t v___x_1426_; size_t v___x_1427_; 
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_i_1413_, v___x_1426_);
v_i_1413_ = v___x_1427_;
goto _start;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_motive_1408_);
v___x_1429_ = lean_box(v___x_1423_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
else
{
uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v_motive_1408_);
v___x_1443_ = 0;
v___x_1444_ = lean_box(v___x_1443_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_1408_ = stack[0].m_obj;
uint8_t v___x_1409_ = stack[1].m_num;
lean_object* v_next_1410_ = stack[2].m_obj;
lean_object* v_upperBound_1411_ = stack[3].m_obj;
lean_object* v_as_1412_ = stack[4].m_obj;
size_t v_i_1413_ = stack[5].m_num;
size_t v_stop_1414_ = stack[6].m_num;
lean_object* v___y_1415_ = stack[7].m_obj;
lean_object* v___y_1416_ = stack[8].m_obj;
lean_object* v___y_1417_ = stack[9].m_obj;
lean_object* v___y_1418_ = stack[10].m_obj;
lean_object* v_res_1446_;
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1408_, v___x_1409_, v_next_1410_, v_upperBound_1411_, v_as_1412_, v_i_1413_, v_stop_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
stack->m_obj
 = v_res_1446_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___boxed(lean_object* v_motive_1447_, lean_object* v___x_1448_, lean_object* v_next_1449_, lean_object* v_upperBound_1450_, lean_object* v_as_1451_, lean_object* v_i_1452_, lean_object* v_stop_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_3821__boxed_1459_; size_t v_i_boxed_1460_; size_t v_stop_boxed_1461_; lean_object* v_res_1462_; 
v___x_3821__boxed_1459_ = lean_unbox(v___x_1448_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_stop_boxed_1461_ = lean_unbox_usize(v_stop_1453_);
lean_dec(v_stop_1453_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1447_, v___x_3821__boxed_1459_, v_next_1449_, v_upperBound_1450_, v_as_1451_, v_i_boxed_1460_, v_stop_boxed_1461_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v_as_1451_);
lean_dec(v_upperBound_1450_);
lean_dec(v_next_1449_);
return v_res_1462_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(lean_object* v_motive_1463_, lean_object* v___x_1464_, uint8_t v___x_1465_, lean_object* v_minorArgs_1466_, lean_object* v_next_1467_, lean_object* v_upperBound_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
if (lean_obj_tag(v_x_1469_) == 5)
{
lean_object* v_fn_1477_; lean_object* v_arg_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_fn_1477_ = lean_ctor_get(v_x_1469_, 0);
lean_inc_ref(v_fn_1477_);
v_arg_1478_ = lean_ctor_get(v_x_1469_, 1);
lean_inc_ref(v_arg_1478_);
lean_dec_ref_known(v_x_1469_, 2);
v___x_1479_ = lean_array_set(v_x_1470_, v_x_1471_, v_arg_1478_);
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_sub(v_x_1471_, v___x_1480_);
lean_dec(v_x_1471_);
v_x_1469_ = v_fn_1477_;
v_x_1470_ = v___x_1479_;
v_x_1471_ = v___x_1481_;
goto _start;
}
else
{
uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v_recursor_1487_; 
lean_dec(v_x_1471_);
lean_dec_ref(v_x_1470_);
v___x_1483_ = lean_expr_eqv(v_x_1469_, v_motive_1463_);
lean_dec_ref(v_x_1469_);
v___x_1484_ = lean_box(v___x_1483_);
v___x_1485_ = lean_array_push(v___x_1464_, v___x_1484_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_array_get_size(v_minorArgs_1466_);
v___x_1493_ = lean_nat_dec_lt(v___x_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_dec_ref(v_motive_1463_);
v_recursor_1487_ = v___x_1493_;
goto v___jp_1486_;
}
else
{
if (v___x_1493_ == 0)
{
lean_dec_ref(v_motive_1463_);
v_recursor_1487_ = v___x_1493_;
goto v___jp_1486_;
}
else
{
size_t v___x_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = ((size_t)0ULL);
v___x_1495_ = lean_usize_of_nat(v___x_1492_);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1463_, v___x_1465_, v_next_1467_, v_upperBound_1468_, v_minorArgs_1466_, v___x_1494_, v___x_1495_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; uint8_t v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_unbox(v_a_1497_);
lean_dec(v_a_1497_);
v_recursor_1487_ = v___x_1498_;
goto v___jp_1486_;
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v___x_1485_);
v_a_1499_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1496_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1496_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_motive_1463_);
v_recursor_1487_ = v___x_1465_;
goto v___jp_1486_;
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = lean_box(v_recursor_1487_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1485_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_1463_ = stack[0].m_obj;
lean_object* v___x_1464_ = stack[1].m_obj;
uint8_t v___x_1465_ = stack[2].m_num;
lean_object* v_minorArgs_1466_ = stack[3].m_obj;
lean_object* v_next_1467_ = stack[4].m_obj;
lean_object* v_upperBound_1468_ = stack[5].m_obj;
lean_object* v_x_1469_ = stack[6].m_obj;
lean_object* v_x_1470_ = stack[7].m_obj;
lean_object* v_x_1471_ = stack[8].m_obj;
lean_object* v___y_1472_ = stack[9].m_obj;
lean_object* v___y_1473_ = stack[10].m_obj;
lean_object* v___y_1474_ = stack[11].m_obj;
lean_object* v___y_1475_ = stack[12].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1463_, v___x_1464_, v___x_1465_, v_minorArgs_1466_, v_next_1467_, v_upperBound_1468_, v_x_1469_, v_x_1470_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1___boxed(lean_object* v_motive_1508_, lean_object* v___x_1509_, lean_object* v___x_1510_, lean_object* v_minorArgs_1511_, lean_object* v_next_1512_, lean_object* v_upperBound_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
uint8_t v___x_3936__boxed_1522_; lean_object* v_res_1523_; 
v___x_3936__boxed_1522_ = lean_unbox(v___x_1510_);
v_res_1523_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1508_, v___x_1509_, v___x_3936__boxed_1522_, v_minorArgs_1511_, v_next_1512_, v_upperBound_1513_, v_x_1514_, v_x_1515_, v_x_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v_upperBound_1513_);
lean_dec(v_next_1512_);
lean_dec_ref(v_minorArgs_1511_);
return v_res_1523_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1524_; lean_object* v_dummy_1525_; 
v___x_1524_ = lean_box(0);
v_dummy_1525_ = l_Lean_Expr_sort___override(v___x_1524_);
return v_dummy_1525_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(lean_object* v_motive_1526_, lean_object* v_fst_1527_, lean_object* v_snd_1528_, lean_object* v_a_1529_, lean_object* v_upperBound_1530_, lean_object* v_minorArgs_1531_, lean_object* v_minorResultType_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_dummy_1538_; lean_object* v_nargs_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; 
v_dummy_1538_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_1539_ = l_Lean_Expr_getAppNumArgs(v_minorResultType_1532_);
lean_inc(v_nargs_1539_);
v___x_1540_ = lean_mk_array(v_nargs_1539_, v_dummy_1538_);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_sub(v_nargs_1539_, v___x_1541_);
lean_dec(v_nargs_1539_);
v___x_1543_ = lean_unbox(v_snd_1528_);
v___x_1544_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1526_, v_fst_1527_, v___x_1543_, v_minorArgs_1531_, v_a_1529_, v_upperBound_1530_, v_minorResultType_1532_, v___x_1540_, v___x_1542_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v___x_1544_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_1526_ = stack[0].m_obj;
lean_object* v_fst_1527_ = stack[1].m_obj;
lean_object* v_snd_1528_ = stack[2].m_obj;
lean_object* v_a_1529_ = stack[3].m_obj;
lean_object* v_upperBound_1530_ = stack[4].m_obj;
lean_object* v_minorArgs_1531_ = stack[5].m_obj;
lean_object* v_minorResultType_1532_ = stack[6].m_obj;
lean_object* v___y_1533_ = stack[7].m_obj;
lean_object* v___y_1534_ = stack[8].m_obj;
lean_object* v___y_1535_ = stack[9].m_obj;
lean_object* v___y_1536_ = stack[10].m_obj;
lean_object* v_res_1545_;
v_res_1545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(v_motive_1526_, v_fst_1527_, v_snd_1528_, v_a_1529_, v_upperBound_1530_, v_minorArgs_1531_, v_minorResultType_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
stack->m_obj
 = v_res_1545_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed(lean_object* v_motive_1546_, lean_object* v_fst_1547_, lean_object* v_snd_1548_, lean_object* v_a_1549_, lean_object* v_upperBound_1550_, lean_object* v_minorArgs_1551_, lean_object* v_minorResultType_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(v_motive_1546_, v_fst_1547_, v_snd_1548_, v_a_1549_, v_upperBound_1550_, v_minorArgs_1551_, v_minorResultType_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_minorArgs_1551_);
lean_dec(v_upperBound_1550_);
lean_dec(v_a_1549_);
lean_dec(v_snd_1548_);
return v_res_1558_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(lean_object* v_upperBound_1559_, lean_object* v_motive_1560_, lean_object* v_xs_1561_, lean_object* v_numParams_1562_, lean_object* v_majorPos_1563_, lean_object* v_numIndices_1564_, lean_object* v_a_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_a_1573_; uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_lt(v_a_1565_, v_upperBound_1559_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec(v_a_1565_);
lean_dec_ref(v_motive_1560_);
lean_dec(v_upperBound_1559_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_b_1566_);
return v___x_1578_;
}
else
{
lean_object* v_fst_1579_; lean_object* v_snd_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1611_; 
v_fst_1579_ = lean_ctor_get(v_b_1566_, 0);
v_snd_1580_ = lean_ctor_get(v_b_1566_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_b_1566_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1582_ = v_b_1566_;
v_isShared_1583_ = v_isSharedCheck_1611_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snd_1580_);
lean_inc(v_fst_1579_);
lean_dec(v_b_1566_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1611_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v_recursor_1586_; 
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = lean_nat_add(v_numParams_1562_, v___x_1584_);
v_recursor_1586_ = lean_nat_dec_lt(v_a_1565_, v___x_1585_);
lean_dec(v___x_1585_);
if (v_recursor_1586_ == 0)
{
lean_object* v___f_1587_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
lean_inc(v_upperBound_1559_);
lean_inc(v_a_1565_);
lean_inc(v_snd_1580_);
lean_inc(v_fst_1579_);
lean_inc_ref(v_motive_1560_);
v___f_1587_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1587_, 0, v_motive_1560_);
lean_closure_set(v___f_1587_, 1, v_fst_1579_);
lean_closure_set(v___f_1587_, 2, v_snd_1580_);
lean_closure_set(v___f_1587_, 3, v_a_1565_);
lean_closure_set(v___f_1587_, 4, v_upperBound_1559_);
v___x_1602_ = lean_nat_sub(v_majorPos_1563_, v_numIndices_1564_);
v___x_1603_ = lean_nat_dec_le(v___x_1602_, v_a_1565_);
lean_dec(v___x_1602_);
if (v___x_1603_ == 0)
{
lean_del_object(v___x_1582_);
lean_dec(v_snd_1580_);
lean_dec(v_fst_1579_);
goto v___jp_1588_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_nat_dec_le(v_a_1565_, v_majorPos_1563_);
if (v___x_1604_ == 0)
{
lean_del_object(v___x_1582_);
lean_dec(v_snd_1580_);
lean_dec(v_fst_1579_);
goto v___jp_1588_;
}
else
{
lean_object* v___x_1606_; 
lean_dec_ref(v___f_1587_);
if (v_isShared_1583_ == 0)
{
v___x_1606_ = v___x_1582_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_fst_1579_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_snd_1580_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v_a_1573_ = v___x_1606_;
goto v___jp_1572_;
}
}
}
v___jp_1588_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_array_fget_borrowed(v_xs_1561_, v_a_1565_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
lean_inc(v___x_1589_);
v___x_1590_ = lean_infer_type(v___x_1589_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_1591_, v___f_1587_, v_recursor_1586_, v_recursor_1586_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v_a_1573_ = v_a_1593_;
goto v___jp_1572_;
}
else
{
lean_dec(v_a_1565_);
lean_dec_ref(v_motive_1560_);
lean_dec(v_upperBound_1559_);
return v___x_1592_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v___f_1587_);
lean_dec(v_a_1565_);
lean_dec_ref(v_motive_1560_);
lean_dec(v_upperBound_1559_);
v_a_1594_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1590_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1590_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
else
{
lean_object* v___x_1609_; 
if (v_isShared_1583_ == 0)
{
v___x_1609_ = v___x_1582_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_fst_1579_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_snd_1580_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_a_1573_ = v___x_1609_;
goto v___jp_1572_;
}
}
}
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_a_1565_, v___x_1574_);
lean_dec(v_a_1565_);
v_a_1565_ = v___x_1575_;
v_b_1566_ = v_a_1573_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1559_ = stack[0].m_obj;
lean_object* v_motive_1560_ = stack[1].m_obj;
lean_object* v_xs_1561_ = stack[2].m_obj;
lean_object* v_numParams_1562_ = stack[3].m_obj;
lean_object* v_majorPos_1563_ = stack[4].m_obj;
lean_object* v_numIndices_1564_ = stack[5].m_obj;
lean_object* v_a_1565_ = stack[6].m_obj;
lean_object* v_b_1566_ = stack[7].m_obj;
lean_object* v___y_1567_ = stack[8].m_obj;
lean_object* v___y_1568_ = stack[9].m_obj;
lean_object* v___y_1569_ = stack[10].m_obj;
lean_object* v___y_1570_ = stack[11].m_obj;
lean_object* v_res_1612_;
v_res_1612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1559_, v_motive_1560_, v_xs_1561_, v_numParams_1562_, v_majorPos_1563_, v_numIndices_1564_, v_a_1565_, v_b_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
stack->m_obj
 = v_res_1612_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___boxed(lean_object* v_upperBound_1613_, lean_object* v_motive_1614_, lean_object* v_xs_1615_, lean_object* v_numParams_1616_, lean_object* v_majorPos_1617_, lean_object* v_numIndices_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1613_, v_motive_1614_, v_xs_1615_, v_numParams_1616_, v_majorPos_1617_, v_numIndices_1618_, v_a_1619_, v_b_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v_numIndices_1618_);
lean_dec(v_majorPos_1617_);
lean_dec(v_numParams_1616_);
lean_dec_ref(v_xs_1615_);
return v_res_1626_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(lean_object* v_xs_1633_, lean_object* v_numParams_1634_, lean_object* v_numIndices_1635_, lean_object* v_majorPos_1636_, lean_object* v_motive_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = lean_array_get_size(v_xs_1633_);
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1));
v___x_1646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v___x_1643_, v_motive_1637_, v_xs_1633_, v_numParams_1634_, v_majorPos_1636_, v_numIndices_1635_, v___x_1644_, v___x_1645_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1664_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1664_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1664_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; lean_object* v_snd_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1663_; 
v_fst_1651_ = lean_ctor_get(v_a_1647_, 0);
v_snd_1652_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1654_ = v_a_1647_;
v_isShared_1655_ = v_isSharedCheck_1663_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_snd_1652_);
lean_inc(v_fst_1651_);
lean_dec(v_a_1647_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1663_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_array_to_list(v_fst_1651_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1656_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_snd_1652_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1658_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1646_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1646_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1633_ = stack[0].m_obj;
lean_object* v_numParams_1634_ = stack[1].m_obj;
lean_object* v_numIndices_1635_ = stack[2].m_obj;
lean_object* v_majorPos_1636_ = stack[3].m_obj;
lean_object* v_motive_1637_ = stack[4].m_obj;
lean_object* v_a_1638_ = stack[5].m_obj;
lean_object* v_a_1639_ = stack[6].m_obj;
lean_object* v_a_1640_ = stack[7].m_obj;
lean_object* v_a_1641_ = stack[8].m_obj;
lean_object* v_res_1673_;
v_res_1673_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1633_, v_numParams_1634_, v_numIndices_1635_, v_majorPos_1636_, v_motive_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
stack->m_obj
 = v_res_1673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(lean_object* v_xs_1674_, lean_object* v_numParams_1675_, lean_object* v_numIndices_1676_, lean_object* v_majorPos_1677_, lean_object* v_motive_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1674_, v_numParams_1675_, v_numIndices_1676_, v_majorPos_1677_, v_motive_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_majorPos_1677_);
lean_dec(v_numIndices_1676_);
lean_dec(v_numParams_1675_);
lean_dec_ref(v_xs_1674_);
return v_res_1684_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(lean_object* v_upperBound_1685_, lean_object* v_motive_1686_, lean_object* v_xs_1687_, lean_object* v_numParams_1688_, lean_object* v_majorPos_1689_, lean_object* v_numIndices_1690_, lean_object* v_inst_1691_, lean_object* v_R_1692_, lean_object* v_a_1693_, lean_object* v_b_1694_, lean_object* v_c_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1685_, v_motive_1686_, v_xs_1687_, v_numParams_1688_, v_majorPos_1689_, v_numIndices_1690_, v_a_1693_, v_b_1694_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1685_ = stack[0].m_obj;
lean_object* v_motive_1686_ = stack[1].m_obj;
lean_object* v_xs_1687_ = stack[2].m_obj;
lean_object* v_numParams_1688_ = stack[3].m_obj;
lean_object* v_majorPos_1689_ = stack[4].m_obj;
lean_object* v_numIndices_1690_ = stack[5].m_obj;
lean_object* v_a_1693_ = stack[8].m_obj;
lean_object* v_b_1694_ = stack[9].m_obj;
lean_object* v___y_1696_ = stack[11].m_obj;
lean_object* v___y_1697_ = stack[12].m_obj;
lean_object* v___y_1698_ = stack[13].m_obj;
lean_object* v___y_1699_ = stack[14].m_obj;
lean_object* v_res_1702_;
v_res_1702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(v_upperBound_1685_, v_motive_1686_, v_xs_1687_, v_numParams_1688_, v_majorPos_1689_, v_numIndices_1690_, lean_box(0), lean_box(0), v_a_1693_, v_b_1694_, lean_box(0), v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___boxed(lean_object* v_upperBound_1703_, lean_object* v_motive_1704_, lean_object* v_xs_1705_, lean_object* v_numParams_1706_, lean_object* v_majorPos_1707_, lean_object* v_numIndices_1708_, lean_object* v_inst_1709_, lean_object* v_R_1710_, lean_object* v_a_1711_, lean_object* v_b_1712_, lean_object* v_c_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(v_upperBound_1703_, v_motive_1704_, v_xs_1705_, v_numParams_1706_, v_majorPos_1707_, v_numIndices_1708_, v_inst_1709_, v_R_1710_, v_a_1711_, v_b_1712_, v_c_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v_numIndices_1708_);
lean_dec(v_majorPos_1707_);
lean_dec(v_numParams_1706_);
lean_dec_ref(v_xs_1705_);
return v_res_1719_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(lean_object* v_declName_1723_, lean_object* v_motiveArgs_1724_, lean_object* v_motiveResultType_1725_, lean_object* v_motiveTypeParams_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = l_Lean_Expr_isSort(v_motiveResultType_1725_);
if (v___x_1740_ == 0)
{
goto v___jp_1732_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = lean_array_get_size(v_motiveArgs_1724_);
v___x_1742_ = lean_array_get_size(v_motiveTypeParams_1726_);
v___x_1743_ = lean_nat_dec_eq(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
goto v___jp_1732_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v_declName_1723_);
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
v___jp_1732_:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1733_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1734_ = 0;
v___x_1735_ = l_Lean_MessageData_ofConstName(v_declName_1723_, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1733_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1738_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1739_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1723_ = stack[0].m_obj;
lean_object* v_motiveArgs_1724_ = stack[1].m_obj;
lean_object* v_motiveResultType_1725_ = stack[2].m_obj;
lean_object* v_motiveTypeParams_1726_ = stack[3].m_obj;
lean_object* v_a_1727_ = stack[4].m_obj;
lean_object* v_a_1728_ = stack[5].m_obj;
lean_object* v_a_1729_ = stack[6].m_obj;
lean_object* v_a_1730_ = stack[7].m_obj;
lean_object* v_res_1746_;
v_res_1746_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1723_, v_motiveArgs_1724_, v_motiveResultType_1725_, v_motiveTypeParams_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(lean_object* v_declName_1747_, lean_object* v_motiveArgs_1748_, lean_object* v_motiveResultType_1749_, lean_object* v_motiveTypeParams_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1747_, v_motiveArgs_1748_, v_motiveResultType_1749_, v_motiveTypeParams_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec_ref(v_motiveTypeParams_1750_);
lean_dec_ref(v_motiveResultType_1749_);
lean_dec_ref(v_motiveArgs_1748_);
return v_res_1756_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(lean_object* v_declName_1757_, lean_object* v_motiveArgs_1758_, lean_object* v_a_1759_, lean_object* v_us_1760_, lean_object* v_xs_1761_, lean_object* v___x_1762_, lean_object* v___y_1763_, lean_object* v_fst_1764_, lean_object* v_motive_1765_, lean_object* v_declName_1766_, uint8_t v_snd_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_motiveTypeParams_1770_, lean_object* v_motiveResultType_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
lean_inc(v_declName_1757_);
v___x_1777_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1757_, v_motiveArgs_1758_, v_motiveResultType_1771_, v_motiveTypeParams_1770_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v___x_1777_, 1);
lean_inc(v_declName_1757_);
v___x_1778_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1757_, v_motiveResultType_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l_Lean_ConstantInfo_levelParams(v_a_1759_);
lean_inc(v_declName_1757_);
v___x_1781_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1757_, v___x_1780_, v_a_1779_, v_us_1760_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v_a_1779_);
lean_dec(v___x_1780_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1783_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1761_, v___x_1762_, v___y_1763_, v_fst_1764_, v_motive_1765_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1796_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1796_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1796_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_fst_1788_; lean_object* v_snd_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1794_; 
v_fst_1788_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_fst_1788_);
v_snd_1789_ = lean_ctor_get(v_a_1784_, 1);
lean_inc(v_snd_1789_);
lean_dec(v_a_1784_);
v___x_1790_ = lean_array_get_size(v_xs_1761_);
v___x_1791_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1791_, 0, v_declName_1757_);
lean_ctor_set(v___x_1791_, 1, v_declName_1766_);
lean_ctor_set(v___x_1791_, 2, v_a_1782_);
lean_ctor_set(v___x_1791_, 3, v___x_1790_);
lean_ctor_set(v___x_1791_, 4, v_fst_1764_);
lean_ctor_set(v___x_1791_, 5, v_a_1768_);
lean_ctor_set(v___x_1791_, 6, v_a_1769_);
lean_ctor_set(v___x_1791_, 7, v_fst_1788_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*8, v_snd_1767_);
v___x_1792_ = lean_unbox(v_snd_1789_);
lean_dec(v_snd_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*8 + 1, v___x_1792_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1791_);
v___x_1794_ = v___x_1786_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1791_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1782_);
lean_dec(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec(v_declName_1766_);
lean_dec(v_fst_1764_);
lean_dec(v_declName_1757_);
v_a_1797_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1783_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1783_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec(v_declName_1766_);
lean_dec_ref(v_motive_1765_);
lean_dec(v_fst_1764_);
lean_dec(v_declName_1757_);
v_a_1805_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1781_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1781_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec(v_declName_1766_);
lean_dec_ref(v_motive_1765_);
lean_dec(v_fst_1764_);
lean_dec(v_us_1760_);
lean_dec(v_declName_1757_);
v_a_1813_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1778_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1778_);
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
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec(v_declName_1766_);
lean_dec_ref(v_motive_1765_);
lean_dec(v_fst_1764_);
lean_dec(v_us_1760_);
lean_dec(v_declName_1757_);
v_a_1821_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1777_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1777_);
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
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1757_ = stack[0].m_obj;
lean_object* v_motiveArgs_1758_ = stack[1].m_obj;
lean_object* v_a_1759_ = stack[2].m_obj;
lean_object* v_us_1760_ = stack[3].m_obj;
lean_object* v_xs_1761_ = stack[4].m_obj;
lean_object* v___x_1762_ = stack[5].m_obj;
lean_object* v___y_1763_ = stack[6].m_obj;
lean_object* v_fst_1764_ = stack[7].m_obj;
lean_object* v_motive_1765_ = stack[8].m_obj;
lean_object* v_declName_1766_ = stack[9].m_obj;
uint8_t v_snd_1767_ = stack[10].m_num;
lean_object* v_a_1768_ = stack[11].m_obj;
lean_object* v_a_1769_ = stack[12].m_obj;
lean_object* v_motiveTypeParams_1770_ = stack[13].m_obj;
lean_object* v_motiveResultType_1771_ = stack[14].m_obj;
lean_object* v___y_1772_ = stack[15].m_obj;
lean_object* v___y_1773_ = stack[16].m_obj;
lean_object* v___y_1774_ = stack[17].m_obj;
lean_object* v___y_1775_ = stack[18].m_obj;
lean_object* v_res_1829_;
v_res_1829_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(v_declName_1757_, v_motiveArgs_1758_, v_a_1759_, v_us_1760_, v_xs_1761_, v___x_1762_, v___y_1763_, v_fst_1764_, v_motive_1765_, v_declName_1766_, v_snd_1767_, v_a_1768_, v_a_1769_, v_motiveTypeParams_1770_, v_motiveResultType_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
stack->m_obj
 = v_res_1829_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v_declName_1830_ = _args[0];
lean_object* v_motiveArgs_1831_ = _args[1];
lean_object* v_a_1832_ = _args[2];
lean_object* v_us_1833_ = _args[3];
lean_object* v_xs_1834_ = _args[4];
lean_object* v___x_1835_ = _args[5];
lean_object* v___y_1836_ = _args[6];
lean_object* v_fst_1837_ = _args[7];
lean_object* v_motive_1838_ = _args[8];
lean_object* v_declName_1839_ = _args[9];
lean_object* v_snd_1840_ = _args[10];
lean_object* v_a_1841_ = _args[11];
lean_object* v_a_1842_ = _args[12];
lean_object* v_motiveTypeParams_1843_ = _args[13];
lean_object* v_motiveResultType_1844_ = _args[14];
lean_object* v___y_1845_ = _args[15];
lean_object* v___y_1846_ = _args[16];
lean_object* v___y_1847_ = _args[17];
lean_object* v___y_1848_ = _args[18];
lean_object* v___y_1849_ = _args[19];
_start:
{
uint8_t v_snd_5076__boxed_1850_; lean_object* v_res_1851_; 
v_snd_5076__boxed_1850_ = lean_unbox(v_snd_1840_);
v_res_1851_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(v_declName_1830_, v_motiveArgs_1831_, v_a_1832_, v_us_1833_, v_xs_1834_, v___x_1835_, v___y_1836_, v_fst_1837_, v_motive_1838_, v_declName_1839_, v_snd_5076__boxed_1850_, v_a_1841_, v_a_1842_, v_motiveTypeParams_1843_, v_motiveResultType_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_motiveResultType_1844_);
lean_dec_ref(v_motiveTypeParams_1843_);
lean_dec(v___y_1836_);
lean_dec(v___x_1835_);
lean_dec_ref(v_xs_1834_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_motiveArgs_1831_);
return v_res_1851_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0));
v___x_1854_ = l_Lean_stringToMessageData(v___x_1853_);
return v___x_1854_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(lean_object* v_declName_1855_, lean_object* v_xs_1856_, lean_object* v___x_1857_, lean_object* v_fst_1858_, lean_object* v___y_1859_, lean_object* v_motiveArgs_1860_, lean_object* v_a_1861_, lean_object* v_motive_1862_, uint8_t v_snd_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
if (lean_obj_tag(v_x_1864_) == 5)
{
lean_object* v_fn_1872_; lean_object* v_arg_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_fn_1872_ = lean_ctor_get(v_x_1864_, 0);
lean_inc_ref(v_fn_1872_);
v_arg_1873_ = lean_ctor_get(v_x_1864_, 1);
lean_inc_ref(v_arg_1873_);
lean_dec_ref_known(v_x_1864_, 2);
v___x_1874_ = lean_array_set(v_x_1865_, v_x_1866_, v_arg_1873_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = lean_nat_sub(v_x_1866_, v___x_1875_);
lean_dec(v_x_1866_);
v_x_1864_ = v_fn_1872_;
v_x_1865_ = v___x_1874_;
v_x_1866_ = v___x_1876_;
goto _start;
}
else
{
lean_dec(v_x_1866_);
if (lean_obj_tag(v_x_1864_) == 4)
{
lean_object* v_declName_1878_; lean_object* v_us_1879_; lean_object* v___x_1880_; 
v_declName_1878_ = lean_ctor_get(v_x_1864_, 0);
lean_inc(v_declName_1878_);
v_us_1879_ = lean_ctor_get(v_x_1864_, 1);
lean_inc(v_us_1879_);
lean_dec_ref_known(v_x_1864_, 2);
lean_inc(v_declName_1855_);
v___x_1880_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_1855_, v_xs_1856_, v___x_1857_, v_x_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
lean_inc(v_declName_1855_);
v___x_1882_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1855_, v_xs_1856_, v_fst_1858_, v___y_1859_, v_x_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec_ref(v_x_1865_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = lean_box(v_snd_1863_);
lean_inc_ref(v_motive_1862_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed), 20, 13);
lean_closure_set(v___f_1885_, 0, v_declName_1855_);
lean_closure_set(v___f_1885_, 1, v_motiveArgs_1860_);
lean_closure_set(v___f_1885_, 2, v_a_1861_);
lean_closure_set(v___f_1885_, 3, v_us_1879_);
lean_closure_set(v___f_1885_, 4, v_xs_1856_);
lean_closure_set(v___f_1885_, 5, v___x_1857_);
lean_closure_set(v___f_1885_, 6, v___y_1859_);
lean_closure_set(v___f_1885_, 7, v_fst_1858_);
lean_closure_set(v___f_1885_, 8, v_motive_1862_);
lean_closure_set(v___f_1885_, 9, v_declName_1878_);
lean_closure_set(v___f_1885_, 10, v___x_1884_);
lean_closure_set(v___f_1885_, 11, v_a_1881_);
lean_closure_set(v___f_1885_, 12, v_a_1883_);
lean_inc(v___y_1870_);
lean_inc_ref(v___y_1869_);
lean_inc(v___y_1868_);
lean_inc_ref(v___y_1867_);
v___x_1886_ = lean_infer_type(v_motive_1862_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v___x_1888_ = 0;
v___x_1889_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_1887_, v___f_1885_, v___x_1888_, v___x_1888_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1889_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v___f_1885_);
v_a_1890_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1886_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1886_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1881_);
lean_dec(v_us_1879_);
lean_dec(v_declName_1878_);
lean_dec_ref(v_motive_1862_);
lean_dec_ref(v_a_1861_);
lean_dec_ref(v_motiveArgs_1860_);
lean_dec(v___y_1859_);
lean_dec(v_fst_1858_);
lean_dec(v___x_1857_);
lean_dec_ref(v_xs_1856_);
lean_dec(v_declName_1855_);
v_a_1898_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1882_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1882_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_us_1879_);
lean_dec(v_declName_1878_);
lean_dec_ref(v_x_1865_);
lean_dec_ref(v_motive_1862_);
lean_dec_ref(v_a_1861_);
lean_dec_ref(v_motiveArgs_1860_);
lean_dec(v___y_1859_);
lean_dec(v_fst_1858_);
lean_dec(v___x_1857_);
lean_dec_ref(v_xs_1856_);
lean_dec(v_declName_1855_);
v_a_1906_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1880_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1880_);
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
else
{
lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_x_1865_);
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_motive_1862_);
lean_dec_ref(v_a_1861_);
lean_dec_ref(v_motiveArgs_1860_);
lean_dec(v___y_1859_);
lean_dec(v_fst_1858_);
lean_dec(v___x_1857_);
lean_dec_ref(v_xs_1856_);
v___x_1914_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1915_ = 0;
v___x_1916_ = l_Lean_MessageData_ofConstName(v_declName_1855_, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1914_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1919_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1855_ = stack[0].m_obj;
lean_object* v_xs_1856_ = stack[1].m_obj;
lean_object* v___x_1857_ = stack[2].m_obj;
lean_object* v_fst_1858_ = stack[3].m_obj;
lean_object* v___y_1859_ = stack[4].m_obj;
lean_object* v_motiveArgs_1860_ = stack[5].m_obj;
lean_object* v_a_1861_ = stack[6].m_obj;
lean_object* v_motive_1862_ = stack[7].m_obj;
uint8_t v_snd_1863_ = stack[8].m_num;
lean_object* v_x_1864_ = stack[9].m_obj;
lean_object* v_x_1865_ = stack[10].m_obj;
lean_object* v_x_1866_ = stack[11].m_obj;
lean_object* v___y_1867_ = stack[12].m_obj;
lean_object* v___y_1868_ = stack[13].m_obj;
lean_object* v___y_1869_ = stack[14].m_obj;
lean_object* v___y_1870_ = stack[15].m_obj;
lean_object* v_res_1921_;
v_res_1921_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1855_, v_xs_1856_, v___x_1857_, v_fst_1858_, v___y_1859_, v_motiveArgs_1860_, v_a_1861_, v_motive_1862_, v_snd_1863_, v_x_1864_, v_x_1865_, v_x_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
stack->m_obj
 = v_res_1921_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___boxed(lean_object** _args){
lean_object* v_declName_1922_ = _args[0];
lean_object* v_xs_1923_ = _args[1];
lean_object* v___x_1924_ = _args[2];
lean_object* v_fst_1925_ = _args[3];
lean_object* v___y_1926_ = _args[4];
lean_object* v_motiveArgs_1927_ = _args[5];
lean_object* v_a_1928_ = _args[6];
lean_object* v_motive_1929_ = _args[7];
lean_object* v_snd_1930_ = _args[8];
lean_object* v_x_1931_ = _args[9];
lean_object* v_x_1932_ = _args[10];
lean_object* v_x_1933_ = _args[11];
lean_object* v___y_1934_ = _args[12];
lean_object* v___y_1935_ = _args[13];
lean_object* v___y_1936_ = _args[14];
lean_object* v___y_1937_ = _args[15];
lean_object* v___y_1938_ = _args[16];
_start:
{
uint8_t v_snd_5310__boxed_1939_; lean_object* v_res_1940_; 
v_snd_5310__boxed_1939_ = lean_unbox(v_snd_1930_);
v_res_1940_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1922_, v_xs_1923_, v___x_1924_, v_fst_1925_, v___y_1926_, v_motiveArgs_1927_, v_a_1928_, v_motive_1929_, v_snd_5310__boxed_1939_, v_x_1931_, v_x_1932_, v_x_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v_res_1940_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0));
v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
return v___x_1943_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(lean_object* v_declName_1944_, lean_object* v_xs_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
if (lean_obj_tag(v_x_1948_) == 5)
{
lean_object* v_fn_1956_; lean_object* v_arg_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_fn_1956_ = lean_ctor_get(v_x_1948_, 0);
lean_inc_ref(v_fn_1956_);
v_arg_1957_ = lean_ctor_get(v_x_1948_, 1);
lean_inc_ref(v_arg_1957_);
lean_dec_ref_known(v_x_1948_, 2);
v___x_1958_ = lean_array_set(v_x_1949_, v_x_1950_, v_arg_1957_);
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_sub(v_x_1950_, v___x_1959_);
lean_dec(v_x_1950_);
v_x_1948_ = v_fn_1956_;
v_x_1949_ = v___x_1958_;
v_x_1950_ = v___x_1960_;
goto _start;
}
else
{
lean_object* v___x_1962_; 
lean_dec(v_x_1950_);
lean_inc(v_declName_1944_);
v___x_1962_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_1944_, v_x_1948_, v_x_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref_known(v___x_1962_, 1);
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(v_xs_1945_, v_x_1948_, v___x_1963_);
lean_inc(v_declName_1944_);
v___x_1965_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_1944_, v_a_1946_, v_xs_1945_, v_x_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v_snd_1967_; lean_object* v_fst_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2028_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v_snd_1967_ = lean_ctor_get(v_a_1966_, 1);
v_fst_1968_ = lean_ctor_get(v_a_1966_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_a_1966_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1970_ = v_a_1966_;
v_isShared_1971_ = v_isSharedCheck_2028_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1968_);
lean_dec(v_a_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2028_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2027_; 
v_fst_1972_ = lean_ctor_get(v_snd_1967_, 0);
v_snd_1973_ = lean_ctor_get(v_snd_1967_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_snd_1967_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1975_ = v_snd_1967_;
v_isShared_1976_ = v_isSharedCheck_2027_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_snd_1973_);
lean_inc(v_fst_1972_);
lean_dec(v_snd_1967_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2027_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_2001_; uint8_t v___x_2022_; 
v___x_2022_ = lean_unbox(v_snd_1973_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_array_get_size(v_x_1949_);
v___y_2001_ = v___x_2023_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_array_get_size(v_x_1949_);
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_nat_sub(v___x_2024_, v___x_2025_);
v___y_2001_ = v___x_2026_;
goto v___jp_2000_;
}
v___jp_1977_:
{
lean_object* v___x_1983_; 
lean_inc(v___y_1982_);
lean_inc_ref(v___y_1981_);
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
v___x_1983_ = lean_infer_type(v_fst_1968_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v_dummy_1985_; lean_object* v_nargs_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v_dummy_1985_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_1986_ = l_Lean_Expr_getAppNumArgs(v_a_1984_);
lean_inc(v_nargs_1986_);
v___x_1987_ = lean_mk_array(v_nargs_1986_, v_dummy_1985_);
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = lean_nat_sub(v_nargs_1986_, v___x_1988_);
lean_dec(v_nargs_1986_);
v___x_1990_ = lean_unbox(v_snd_1973_);
lean_dec(v_snd_1973_);
v___x_1991_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1944_, v_xs_1945_, v___x_1964_, v_fst_1972_, v___y_1978_, v_x_1949_, v_a_1947_, v_x_1948_, v___x_1990_, v_a_1984_, v___x_1987_, v___x_1989_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v___x_1991_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v___y_1978_);
lean_dec(v_snd_1973_);
lean_dec(v_fst_1972_);
lean_dec(v___x_1964_);
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_x_1948_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_xs_1945_);
lean_dec(v_declName_1944_);
v_a_1992_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1983_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1983_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
v___jp_2000_:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_nat_dec_lt(v_fst_1972_, v___y_2001_);
if (v___x_2002_ == 0)
{
lean_del_object(v___x_1975_);
lean_del_object(v___x_1970_);
v___y_1978_ = v___y_2001_;
v___y_1979_ = v___y_1951_;
v___y_1980_ = v___y_1952_;
v___y_1981_ = v___y_1953_;
v___y_1982_ = v___y_1954_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
lean_dec(v___y_2001_);
lean_dec(v_snd_1973_);
lean_dec(v_fst_1972_);
lean_dec(v_fst_1968_);
lean_dec(v___x_1964_);
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_x_1948_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_xs_1945_);
v___x_2003_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_2004_ = 0;
v___x_2005_ = l_Lean_MessageData_ofConstName(v_declName_1944_, v___x_2004_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 7);
lean_ctor_set(v___x_1975_, 1, v___x_2005_);
lean_ctor_set(v___x_1975_, 0, v___x_2003_);
v___x_2007_ = v___x_1975_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 7);
lean_ctor_set(v___x_1970_, 1, v___x_2008_);
lean_ctor_set(v___x_1970_, 0, v___x_2007_);
v___x_2010_ = v___x_1970_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v___x_2011_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_2010_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
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
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_1964_);
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_x_1948_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_xs_1945_);
lean_dec(v_declName_1944_);
v_a_2029_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1965_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1965_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_x_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_xs_1945_);
lean_dec(v_declName_1944_);
v_a_2037_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1962_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1962_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1944_ = stack[0].m_obj;
lean_object* v_xs_1945_ = stack[1].m_obj;
lean_object* v_a_1946_ = stack[2].m_obj;
lean_object* v_a_1947_ = stack[3].m_obj;
lean_object* v_x_1948_ = stack[4].m_obj;
lean_object* v_x_1949_ = stack[5].m_obj;
lean_object* v_x_1950_ = stack[6].m_obj;
lean_object* v___y_1951_ = stack[7].m_obj;
lean_object* v___y_1952_ = stack[8].m_obj;
lean_object* v___y_1953_ = stack[9].m_obj;
lean_object* v___y_1954_ = stack[10].m_obj;
lean_object* v_res_2045_;
v_res_2045_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_1944_, v_xs_1945_, v_a_1946_, v_a_1947_, v_x_1948_, v_x_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___boxed(lean_object* v_declName_2046_, lean_object* v_xs_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_2046_, v_xs_2047_, v_a_2048_, v_a_2049_, v_x_2050_, v_x_2051_, v_x_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(lean_object* v_declName_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_xs_2062_, lean_object* v_type_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_dummy_2069_; lean_object* v_nargs_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_dummy_2069_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_2070_ = l_Lean_Expr_getAppNumArgs(v_type_2063_);
lean_inc(v_nargs_2070_);
v___x_2071_ = lean_mk_array(v_nargs_2070_, v_dummy_2069_);
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_sub(v_nargs_2070_, v___x_2072_);
lean_dec(v_nargs_2070_);
v___x_2074_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_2059_, v_xs_2062_, v_a_2060_, v_a_2061_, v_type_2063_, v___x_2071_, v___x_2073_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
return v___x_2074_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2059_ = stack[0].m_obj;
lean_object* v_a_2060_ = stack[1].m_obj;
lean_object* v_a_2061_ = stack[2].m_obj;
lean_object* v_xs_2062_ = stack[3].m_obj;
lean_object* v_type_2063_ = stack[4].m_obj;
lean_object* v___y_2064_ = stack[5].m_obj;
lean_object* v___y_2065_ = stack[6].m_obj;
lean_object* v___y_2066_ = stack[7].m_obj;
lean_object* v___y_2067_ = stack[8].m_obj;
lean_object* v_res_2075_;
v_res_2075_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(v_declName_2059_, v_a_2060_, v_a_2061_, v_xs_2062_, v_type_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
stack->m_obj
 = v_res_2075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed(lean_object* v_declName_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_xs_2079_, lean_object* v_type_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(v_declName_2076_, v_a_2077_, v_a_2078_, v_xs_2079_, v_type_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2086_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_2087_, lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_toCold_2094_; lean_object* v_currRecDepth_2095_; lean_object* v_ref_2096_; uint16_t v_optionFlags_2097_; uint8_t v_suppressElabErrors_2098_; uint8_t v_isRecordingDeps_2099_; lean_object* v_ref_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_toCold_2094_ = lean_ctor_get(v___y_2091_, 0);
v_currRecDepth_2095_ = lean_ctor_get(v___y_2091_, 1);
v_ref_2096_ = lean_ctor_get(v___y_2091_, 2);
v_optionFlags_2097_ = lean_ctor_get_uint16(v___y_2091_, sizeof(void*)*3);
v_suppressElabErrors_2098_ = lean_ctor_get_uint8(v___y_2091_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2099_ = lean_ctor_get_uint8(v___y_2091_, sizeof(void*)*3 + 3);
v_ref_2100_ = l_Lean_replaceRef(v_ref_2087_, v_ref_2096_);
lean_inc(v_currRecDepth_2095_);
lean_inc_ref(v_toCold_2094_);
v___x_2101_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2101_, 0, v_toCold_2094_);
lean_ctor_set(v___x_2101_, 1, v_currRecDepth_2095_);
lean_ctor_set(v___x_2101_, 2, v_ref_2100_);
lean_ctor_set_uint16(v___x_2101_, sizeof(void*)*3, v_optionFlags_2097_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*3 + 2, v_suppressElabErrors_2098_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*3 + 3, v_isRecordingDeps_2099_);
v___x_2102_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_2088_, v___y_2089_, v___y_2090_, v___x_2101_, v___y_2092_);
lean_dec_ref_known(v___x_2101_, 3);
return v___x_2102_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2087_ = stack[0].m_obj;
lean_object* v_msg_2088_ = stack[1].m_obj;
lean_object* v___y_2089_ = stack[2].m_obj;
lean_object* v___y_2090_ = stack[3].m_obj;
lean_object* v___y_2091_ = stack[4].m_obj;
lean_object* v___y_2092_ = stack[5].m_obj;
lean_object* v_res_2103_;
v_res_2103_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2087_, v_msg_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
stack->m_obj
 = v_res_2103_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_2104_, lean_object* v_msg_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2104_, v_msg_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_ref_2104_);
return v_res_2111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
lean_ctor_set(v___x_2118_, 2, v___x_2117_);
lean_ctor_set(v___x_2118_, 3, v___x_2117_);
lean_ctor_set(v___x_2118_, 4, v___x_2116_);
lean_ctor_set(v___x_2118_, 5, v___x_2116_);
lean_ctor_set(v___x_2118_, 6, v___x_2116_);
lean_ctor_set(v___x_2118_, 7, v___x_2116_);
lean_ctor_set(v___x_2118_, 8, v___x_2116_);
lean_ctor_set(v___x_2118_, 9, v___x_2116_);
lean_ctor_set(v___x_2118_, 10, v___x_2116_);
lean_ctor_set(v___x_2118_, 11, v___x_2115_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_unsigned_to_nat(32u);
v___x_2120_ = lean_mk_empty_array_with_capacity(v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2122_ = ((size_t)5ULL);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_unsigned_to_nat(32u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_2127_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v___x_2123_);
lean_ctor_set(v___x_2127_, 3, v___x_2123_);
lean_ctor_set_usize(v___x_2127_, 4, v___x_2122_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_box(1);
v___x_2129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2128_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_2137_ = l_Lean_stringToMessageData(v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_2140_ = l_Lean_stringToMessageData(v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22));
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24));
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26));
v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
return v___x_2164_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_2165_, lean_object* v_declHint_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_env_2171_; uint8_t v___x_2172_; 
v___x_2169_ = lean_box(0);
v___x_2170_ = lean_st_ref_get(v___y_2167_);
v_env_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc_ref(v_env_2171_);
lean_dec(v___x_2170_);
v___x_2172_ = l_Lean_Name_isAnonymous(v_declHint_2166_);
if (v___x_2172_ == 0)
{
uint8_t v_isExporting_2173_; 
v_isExporting_2173_ = lean_ctor_get_uint8(v_env_2171_, sizeof(void*)*13);
if (v_isExporting_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec_ref(v_env_2171_);
lean_dec(v_declHint_2166_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_msg_2165_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; uint8_t v___x_2176_; 
lean_inc_ref(v_env_2171_);
v___x_2175_ = l_Lean_Environment_setExporting(v_env_2171_, v___x_2172_);
lean_inc(v_declHint_2166_);
lean_inc_ref(v___x_2175_);
v___x_2176_ = l_Lean_Environment_contains(v___x_2175_, v_declHint_2166_, v_isExporting_2173_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v___x_2175_);
lean_dec_ref(v_env_2171_);
lean_dec(v_declHint_2166_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_msg_2165_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_c_2183_; lean_object* v___x_2184_; 
v___x_2178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_2180_ = l_Lean_Options_empty;
v___x_2181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2175_);
lean_ctor_set(v___x_2181_, 1, v___x_2178_);
lean_ctor_set(v___x_2181_, 2, v___x_2179_);
lean_ctor_set(v___x_2181_, 3, v___x_2180_);
lean_inc(v_declHint_2166_);
v___x_2182_ = l_Lean_MessageData_ofConstName(v_declHint_2166_, v___x_2172_);
v_c_2183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2183_, 0, v___x_2181_);
lean_ctor_set(v_c_2183_, 1, v___x_2182_);
v___x_2184_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2171_, v_declHint_2166_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref(v_env_2171_);
lean_dec(v_declHint_2166_);
v___x_2185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v_c_2183_);
v___x_2187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_MessageData_note(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_msg_2165_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
else
{
lean_object* v_val_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2248_; 
v_val_2192_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2194_ = v___x_2184_;
v_isShared_2195_ = v_isSharedCheck_2248_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_val_2192_);
lean_dec(v___x_2184_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2248_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v_modules_2197_; lean_object* v_moduleNames_2198_; lean_object* v_mod_2199_; uint8_t v___y_2201_; uint8_t v___x_2231_; 
v___x_2196_ = l_Lean_Environment_header(v_env_2171_);
lean_dec_ref(v_env_2171_);
v_modules_2197_ = lean_ctor_get(v___x_2196_, 3);
lean_inc_ref(v_modules_2197_);
v_moduleNames_2198_ = lean_ctor_get(v___x_2196_, 4);
lean_inc_ref(v_moduleNames_2198_);
lean_dec_ref(v___x_2196_);
v_mod_2199_ = lean_array_get(v___x_2169_, v_moduleNames_2198_, v_val_2192_);
lean_dec_ref(v_moduleNames_2198_);
v___x_2231_ = l_Lean_isPrivateName(v_declHint_2166_);
lean_dec(v_declHint_2166_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_array_get_size(v_modules_2197_);
v___x_2233_ = lean_nat_dec_lt(v_val_2192_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v_modules_2197_);
lean_dec(v_val_2192_);
v___y_2201_ = v___x_2231_;
goto v___jp_2200_;
}
else
{
lean_object* v___x_2234_; lean_object* v_toImport_2235_; uint8_t v_isExported_2236_; 
v___x_2234_ = lean_array_fget(v_modules_2197_, v_val_2192_);
lean_dec(v_val_2192_);
lean_dec_ref(v_modules_2197_);
v_toImport_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_toImport_2235_);
lean_dec(v___x_2234_);
v_isExported_2236_ = lean_ctor_get_uint8(v_toImport_2235_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2235_);
v___y_2201_ = v_isExported_2236_;
goto v___jp_2200_;
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec_ref(v_modules_2197_);
lean_del_object(v___x_2194_);
lean_dec(v_val_2192_);
v___x_2237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v_c_2183_);
v___x_2239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25);
v___x_2240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_MessageData_ofName(v_mod_2199_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_MessageData_note(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v_msg_2165_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
return v___x_2247_;
}
v___jp_2200_:
{
if (v___y_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v_c_2183_);
v___x_2204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = l_Lean_MessageData_ofName(v_mod_2199_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_MessageData_note(v___x_2209_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_msg_2165_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2211_);
v___x_2213_ = v___x_2194_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
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
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_c_2183_);
v___x_2217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_Lean_MessageData_ofName(v_mod_2199_);
lean_inc_ref(v___x_2219_);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2219_);
v___x_2224_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23);
v___x_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = l_Lean_MessageData_note(v___x_2225_);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_msg_2165_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2227_);
v___x_2229_ = v___x_2194_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
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
lean_object* v___x_2249_; 
lean_dec_ref(v_env_2171_);
lean_dec(v_declHint_2166_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_msg_2165_);
return v___x_2249_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2165_ = stack[0].m_obj;
lean_object* v_declHint_2166_ = stack[1].m_obj;
lean_object* v___y_2167_ = stack[2].m_obj;
lean_object* v_res_2250_;
v_res_2250_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2165_, v_declHint_2166_, v___y_2167_);
stack->m_obj
 = v_res_2250_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2251_, lean_object* v_declHint_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2251_, v_declHint_2252_, v___y_2253_);
lean_dec(v___y_2253_);
return v_res_2255_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_2256_, lean_object* v_declHint_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2273_; 
v___x_2263_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2256_, v_declHint_2257_, v___y_2261_);
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2273_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2273_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2268_ = l_Lean_unknownIdentifierMessageTag;
v___x_2269_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v_a_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2256_ = stack[0].m_obj;
lean_object* v_declHint_2257_ = stack[1].m_obj;
lean_object* v___y_2258_ = stack[2].m_obj;
lean_object* v___y_2259_ = stack[3].m_obj;
lean_object* v___y_2260_ = stack[4].m_obj;
lean_object* v___y_2261_ = stack[5].m_obj;
lean_object* v_res_2274_;
v_res_2274_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2256_, v_declHint_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
stack->m_obj
 = v_res_2274_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_2275_, lean_object* v_declHint_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2275_, v_declHint_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2283_, lean_object* v_msg_2284_, lean_object* v_declHint_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v_a_2292_; lean_object* v___x_2293_; 
v___x_2291_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2284_, v_declHint_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2283_, v_a_2292_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2293_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2283_ = stack[0].m_obj;
lean_object* v_msg_2284_ = stack[1].m_obj;
lean_object* v_declHint_2285_ = stack[2].m_obj;
lean_object* v___y_2286_ = stack[3].m_obj;
lean_object* v___y_2287_ = stack[4].m_obj;
lean_object* v___y_2288_ = stack[5].m_obj;
lean_object* v___y_2289_ = stack[6].m_obj;
lean_object* v_res_2294_;
v_res_2294_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2283_, v_msg_2284_, v_declHint_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
stack->m_obj
 = v_res_2294_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2295_, lean_object* v_msg_2296_, lean_object* v_declHint_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2295_, v_msg_2296_, v_declHint_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v_ref_2295_);
return v_res_2303_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2306_ = l_Lean_stringToMessageData(v___x_2305_);
return v___x_2306_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2307_, lean_object* v_constName_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2314_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2315_ = 0;
lean_inc(v_constName_2308_);
v___x_2316_ = l_Lean_MessageData_ofConstName(v_constName_2308_, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2307_, v___x_2319_, v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
return v___x_2320_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2307_ = stack[0].m_obj;
lean_object* v_constName_2308_ = stack[1].m_obj;
lean_object* v___y_2309_ = stack[2].m_obj;
lean_object* v___y_2310_ = stack[3].m_obj;
lean_object* v___y_2311_ = stack[4].m_obj;
lean_object* v___y_2312_ = stack[5].m_obj;
lean_object* v_res_2321_;
v_res_2321_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2307_, v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
stack->m_obj
 = v_res_2321_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2322_, lean_object* v_constName_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2322_, v_constName_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v_ref_2322_);
return v_res_2329_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(lean_object* v_constName_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_ref_2336_; lean_object* v___x_2337_; 
v_ref_2336_ = lean_ctor_get(v___y_2333_, 2);
v___x_2337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2336_, v_constName_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2337_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2330_ = stack[0].m_obj;
lean_object* v___y_2331_ = stack[1].m_obj;
lean_object* v___y_2332_ = stack[2].m_obj;
lean_object* v___y_2333_ = stack[3].m_obj;
lean_object* v___y_2334_ = stack[4].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(lean_object* v_constName_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_env_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2352_ = lean_st_ref_get(v___y_2350_);
v_env_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_env_2353_);
lean_dec(v___x_2352_);
v___x_2354_ = 0;
lean_inc(v_constName_2346_);
v___x_2355_ = l_Lean_Environment_find_x3f(v_env_2353_, v_constName_2346_, v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2356_;
}
else
{
lean_object* v_val_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_constName_2346_);
v_val_2357_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2355_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_val_2357_);
lean_dec(v___x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set_tag(v___x_2359_, 0);
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_val_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2346_ = stack[0].m_obj;
lean_object* v___y_2347_ = stack[1].m_obj;
lean_object* v___y_2348_ = stack[2].m_obj;
lean_object* v___y_2349_ = stack[3].m_obj;
lean_object* v___y_2350_ = stack[4].m_obj;
lean_object* v_res_2365_;
v_res_2365_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_constName_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
stack->m_obj
 = v_res_2365_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0___boxed(lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_constName_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2372_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(lean_object* v_declName_2373_, lean_object* v_majorPos_x3f_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2380_; 
lean_inc(v_declName_2373_);
v___x_2380_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_declName_2373_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
lean_inc(v_declName_2373_);
v___x_2382_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_2373_, v_majorPos_x3f_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
lean_inc(v_a_2381_);
v___f_2384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2384_, 0, v_declName_2373_);
lean_closure_set(v___f_2384_, 1, v_a_2383_);
lean_closure_set(v___f_2384_, 2, v_a_2381_);
v___x_2385_ = l_Lean_ConstantInfo_type(v_a_2381_);
lean_dec(v_a_2381_);
v___x_2386_ = 0;
v___x_2387_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v___x_2385_, v___f_2384_, v___x_2386_, v___x_2386_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2387_;
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2381_);
lean_dec(v_declName_2373_);
v_a_2388_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2382_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2382_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_majorPos_x3f_2374_);
lean_dec(v_declName_2373_);
v_a_2396_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2380_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2380_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2373_ = stack[0].m_obj;
lean_object* v_majorPos_x3f_2374_ = stack[1].m_obj;
lean_object* v_a_2375_ = stack[2].m_obj;
lean_object* v_a_2376_ = stack[3].m_obj;
lean_object* v_a_2377_ = stack[4].m_obj;
lean_object* v_a_2378_ = stack[5].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2373_, v_majorPos_x3f_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___boxed(lean_object* v_declName_2405_, lean_object* v_majorPos_x3f_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2405_, v_majorPos_x3f_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
return v_res_2412_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(lean_object* v_00_u03b1_2413_, lean_object* v_constName_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2414_ = stack[1].m_obj;
lean_object* v___y_2415_ = stack[2].m_obj;
lean_object* v___y_2416_ = stack[3].m_obj;
lean_object* v___y_2417_ = stack[4].m_obj;
lean_object* v___y_2418_ = stack[5].m_obj;
lean_object* v_res_2421_;
v_res_2421_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(lean_box(0), v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
stack->m_obj
 = v_res_2421_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2422_, lean_object* v_constName_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(v_00_u03b1_2422_, v_constName_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2429_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2430_, lean_object* v_ref_2431_, lean_object* v_constName_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2431_, v_constName_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v___x_2438_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2431_ = stack[1].m_obj;
lean_object* v_constName_2432_ = stack[2].m_obj;
lean_object* v___y_2433_ = stack[3].m_obj;
lean_object* v___y_2434_ = stack[4].m_obj;
lean_object* v___y_2435_ = stack[5].m_obj;
lean_object* v___y_2436_ = stack[6].m_obj;
lean_object* v_res_2439_;
v_res_2439_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(lean_box(0), v_ref_2431_, v_constName_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
stack->m_obj
 = v_res_2439_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2440_, lean_object* v_ref_2441_, lean_object* v_constName_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(v_00_u03b1_2440_, v_ref_2441_, v_constName_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_ref_2441_);
return v_res_2448_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2449_, lean_object* v_ref_2450_, lean_object* v_msg_2451_, lean_object* v_declHint_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2450_, v_msg_2451_, v_declHint_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2450_ = stack[1].m_obj;
lean_object* v_msg_2451_ = stack[2].m_obj;
lean_object* v_declHint_2452_ = stack[3].m_obj;
lean_object* v___y_2453_ = stack[4].m_obj;
lean_object* v___y_2454_ = stack[5].m_obj;
lean_object* v___y_2455_ = stack[6].m_obj;
lean_object* v___y_2456_ = stack[7].m_obj;
lean_object* v_res_2459_;
v_res_2459_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(lean_box(0), v_ref_2450_, v_msg_2451_, v_declHint_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
stack->m_obj
 = v_res_2459_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_ref_2461_, lean_object* v_msg_2462_, lean_object* v_declHint_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2460_, v_ref_2461_, v_msg_2462_, v_declHint_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v_ref_2461_);
return v_res_2469_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_2470_, lean_object* v_declHint_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2470_, v_declHint_2471_, v___y_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2470_ = stack[0].m_obj;
lean_object* v_declHint_2471_ = stack[1].m_obj;
lean_object* v___y_2472_ = stack[2].m_obj;
lean_object* v___y_2473_ = stack[3].m_obj;
lean_object* v___y_2474_ = stack[4].m_obj;
lean_object* v___y_2475_ = stack[5].m_obj;
lean_object* v_res_2478_;
v_res_2478_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2470_, v_declHint_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
stack->m_obj
 = v_res_2478_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2479_, lean_object* v_declHint_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2479_, v_declHint_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2486_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2487_, lean_object* v_ref_2488_, lean_object* v_msg_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2488_, v_msg_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2488_ = stack[1].m_obj;
lean_object* v_msg_2489_ = stack[2].m_obj;
lean_object* v___y_2490_ = stack[3].m_obj;
lean_object* v___y_2491_ = stack[4].m_obj;
lean_object* v___y_2492_ = stack[5].m_obj;
lean_object* v___y_2493_ = stack[6].m_obj;
lean_object* v_res_2496_;
v_res_2496_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(lean_box(0), v_ref_2488_, v_msg_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
stack->m_obj
 = v_res_2496_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_ref_2498_, lean_object* v_msg_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2497_, v_ref_2498_, v_msg_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v_ref_2498_);
return v_res_2505_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(lean_object* v_msgData_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v_toCold_2511_; lean_object* v_env_2512_; lean_object* v_options_2513_; uint8_t v___x_2514_; lean_object* v_env_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2510_ = lean_st_ref_get(v___y_2508_);
v_toCold_2511_ = lean_ctor_get(v___y_2507_, 0);
v_env_2512_ = lean_ctor_get(v___x_2510_, 0);
lean_inc_ref(v_env_2512_);
lean_dec(v___x_2510_);
v_options_2513_ = lean_ctor_get(v_toCold_2511_, 2);
v___x_2514_ = 0;
v_env_2515_ = l_Lean_Environment_setRecordingDeps(v_env_2512_, v___x_2514_);
v___x_2516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2517_ = lean_unsigned_to_nat(32u);
v___x_2518_ = lean_mk_empty_array_with_capacity(v___x_2517_);
lean_dec_ref(v___x_2518_);
v___x_2519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2513_);
v___x_2520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2520_, 0, v_env_2515_);
lean_ctor_set(v___x_2520_, 1, v___x_2516_);
lean_ctor_set(v___x_2520_, 2, v___x_2519_);
lean_ctor_set(v___x_2520_, 3, v_options_2513_);
v___x_2521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_msgData_2506_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2506_ = stack[0].m_obj;
lean_object* v___y_2507_ = stack[1].m_obj;
lean_object* v___y_2508_ = stack[2].m_obj;
lean_object* v_res_2523_;
v_res_2523_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msgData_2506_, v___y_2507_, v___y_2508_);
stack->m_obj
 = v_res_2523_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msgData_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2528_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_ref_2533_; lean_object* v___x_2534_; lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2543_; 
v_ref_2533_ = lean_ctor_get(v___y_2530_, 2);
v___x_2534_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msg_2529_, v___y_2530_, v___y_2531_);
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_inc(v_ref_2533_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_ref_2533_);
lean_ctor_set(v___x_2539_, 1, v_a_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set_tag(v___x_2537_, 1);
lean_ctor_set(v___x_2537_, 0, v___x_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2529_ = stack[0].m_obj;
lean_object* v___y_2530_ = stack[1].m_obj;
lean_object* v___y_2531_ = stack[2].m_obj;
lean_object* v_res_2544_;
v_res_2544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2529_, v___y_2530_, v___y_2531_);
stack->m_obj
 = v_res_2544_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2549_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(lean_object* v_ref_2550_, lean_object* v_msg_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_toCold_2555_; lean_object* v_currRecDepth_2556_; lean_object* v_ref_2557_; uint16_t v_optionFlags_2558_; uint8_t v_suppressElabErrors_2559_; uint8_t v_isRecordingDeps_2560_; lean_object* v_ref_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_toCold_2555_ = lean_ctor_get(v___y_2552_, 0);
v_currRecDepth_2556_ = lean_ctor_get(v___y_2552_, 1);
v_ref_2557_ = lean_ctor_get(v___y_2552_, 2);
v_optionFlags_2558_ = lean_ctor_get_uint16(v___y_2552_, sizeof(void*)*3);
v_suppressElabErrors_2559_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2560_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*3 + 3);
v_ref_2561_ = l_Lean_replaceRef(v_ref_2550_, v_ref_2557_);
lean_inc(v_currRecDepth_2556_);
lean_inc_ref(v_toCold_2555_);
v___x_2562_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2562_, 0, v_toCold_2555_);
lean_ctor_set(v___x_2562_, 1, v_currRecDepth_2556_);
lean_ctor_set(v___x_2562_, 2, v_ref_2561_);
lean_ctor_set_uint16(v___x_2562_, sizeof(void*)*3, v_optionFlags_2558_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*3 + 2, v_suppressElabErrors_2559_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*3 + 3, v_isRecordingDeps_2560_);
v___x_2563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2551_, v___x_2562_, v___y_2553_);
lean_dec_ref_known(v___x_2562_, 3);
return v___x_2563_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2550_ = stack[0].m_obj;
lean_object* v_msg_2551_ = stack[1].m_obj;
lean_object* v___y_2552_ = stack[2].m_obj;
lean_object* v___y_2553_ = stack[3].m_obj;
lean_object* v_res_2564_;
v_res_2564_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2550_, v_msg_2551_, v___y_2552_, v___y_2553_);
stack->m_obj
 = v_res_2564_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg___boxed(lean_object* v_ref_2565_, lean_object* v_msg_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2565_, v_msg_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v_ref_2565_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5));
v___x_2582_ = l_Lean_stringToMessageData(v___x_2581_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7));
v___x_2585_ = l_Lean_stringToMessageData(v___x_2584_);
return v___x_2585_;
}
}
lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos(lean_object* v_stx_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
lean_inc(v_stx_2586_);
v___x_2590_ = l_Lean_Syntax_getKind(v_stx_2586_);
v___x_2591_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4));
v___x_2592_ = lean_name_eq(v___x_2590_, v___x_2591_);
lean_dec(v___x_2590_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_obj_once(&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6, &l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6_once, _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6);
v___x_2594_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_2586_, v___x_2593_, v_a_2587_, v_a_2588_);
lean_dec(v_stx_2586_);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v___y_2597_; lean_object* v___y_2601_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2614_ = l_Lean_Syntax_getArg(v_stx_2586_, v___x_2595_);
v___x_2615_ = l_Lean_Syntax_isNatLit_x3f(v___x_2614_);
lean_dec(v___x_2614_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_unsigned_to_nat(0u);
v___y_2601_ = v___x_2616_;
goto v___jp_2600_;
}
else
{
lean_object* v_val_2617_; 
v_val_2617_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v___x_2615_, 1);
v___y_2601_ = v_val_2617_;
goto v___jp_2600_;
}
v___jp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_nat_sub(v___y_2597_, v___x_2595_);
lean_dec(v___y_2597_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
v___jp_2600_:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_nat_dec_eq(v___y_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_dec(v_stx_2586_);
v___y_2597_ = v___y_2601_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v___y_2601_);
v___x_2604_ = lean_obj_once(&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8, &l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8_once, _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8);
v___x_2605_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_2586_, v___x_2604_, v_a_2587_, v_a_2588_);
lean_dec(v_stx_2586_);
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Attribute_Recursor_getMajorPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2586_ = stack[0].m_obj;
lean_object* v_a_2587_ = stack[1].m_obj;
lean_object* v_a_2588_ = stack[2].m_obj;
lean_object* v_res_2618_;
v_res_2618_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2586_, v_a_2587_, v_a_2588_);
stack->m_obj
 = v_res_2618_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(lean_object* v_stx_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2619_, v_a_2620_, v_a_2621_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
return v_res_2623_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(lean_object* v_00_u03b1_2624_, lean_object* v_ref_2625_, lean_object* v_msg_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2625_, v_msg_2626_, v___y_2627_, v___y_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2625_ = stack[1].m_obj;
lean_object* v_msg_2626_ = stack[2].m_obj;
lean_object* v___y_2627_ = stack[3].m_obj;
lean_object* v___y_2628_ = stack[4].m_obj;
lean_object* v_res_2631_;
v_res_2631_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(lean_box(0), v_ref_2625_, v_msg_2626_, v___y_2627_, v___y_2628_);
stack->m_obj
 = v_res_2631_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_ref_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(v_00_u03b1_2632_, v_ref_2633_, v_msg_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v_ref_2633_);
return v_res_2638_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(lean_object* v_00_u03b1_2639_, lean_object* v_msg_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2640_, v___y_2641_, v___y_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2640_ = stack[1].m_obj;
lean_object* v___y_2641_ = stack[2].m_obj;
lean_object* v___y_2642_ = stack[3].m_obj;
lean_object* v_res_2645_;
v_res_2645_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(lean_box(0), v_msg_2640_, v___y_2641_, v___y_2642_);
stack->m_obj
 = v_res_2645_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_msg_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(v_00_u03b1_2646_, v_msg_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2651_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v_x_2652_, lean_object* v_stx_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2653_, v___y_2654_, v___y_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2652_ = stack[0].m_obj;
lean_object* v_stx_2653_ = stack[1].m_obj;
lean_object* v___y_2654_ = stack[2].m_obj;
lean_object* v___y_2655_ = stack[3].m_obj;
lean_object* v_res_2658_;
v_res_2658_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_x_2652_, v_stx_2653_, v___y_2654_, v___y_2655_);
stack->m_obj
 = v_res_2658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_x_2659_, lean_object* v_stx_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_x_2659_, v_stx_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v_x_2659_);
return v_res_2664_;
}
}
uint8_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v_env_2665_, lean_object* v_n_2666_, lean_object* v_x_2667_){
_start:
{
uint8_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = 1;
v___x_2669_ = l_Lean_Environment_contains(v_env_2665_, v_n_2666_, v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2665_ = stack[0].m_obj;
lean_object* v_n_2666_ = stack[1].m_obj;
lean_object* v_x_2667_ = stack[2].m_obj;
uint8_t v_res_2670_;
v_res_2670_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_env_2665_, v_n_2666_, v_x_2667_);
stack->m_num = v_res_2670_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_env_2671_, lean_object* v_n_2672_, lean_object* v_x_2673_){
_start:
{
uint8_t v_res_2674_; lean_object* v_r_2675_; 
v_res_2674_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_env_2671_, v_n_2672_, v_x_2673_);
lean_dec(v_x_2673_);
v_r_2675_ = lean_box(v_res_2674_);
return v_r_2675_;
}
}
static uint64_t _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2682_; uint64_t v___x_2683_; 
v___x_2682_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2683_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_uint64_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2686_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set_uint64(v___x_2686_, sizeof(void*)*1, v___x_2684_);
return v___x_2686_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2689_ = lean_box(1);
v___x_2690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2691_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v___x_2690_);
lean_ctor_set(v___x_2692_, 2, v___x_2689_);
return v___x_2692_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2695_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2696_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
lean_ctor_set(v___x_2698_, 3, v___x_2697_);
lean_ctor_set(v___x_2698_, 4, v___x_2696_);
lean_ctor_set(v___x_2698_, 5, v___x_2696_);
lean_ctor_set(v___x_2698_, 6, v___x_2696_);
lean_ctor_set(v___x_2698_, 7, v___x_2696_);
lean_ctor_set(v___x_2698_, 8, v___x_2696_);
lean_ctor_set(v___x_2698_, 9, v___x_2696_);
lean_ctor_set(v___x_2698_, 10, v___x_2696_);
lean_ctor_set(v___x_2698_, 11, v___x_2695_);
return v___x_2698_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2700_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
lean_ctor_set(v___x_2700_, 3, v___x_2699_);
lean_ctor_set(v___x_2700_, 4, v___x_2699_);
lean_ctor_set(v___x_2700_, 5, v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_ctor_set(v___x_2702_, 2, v___x_2701_);
lean_ctor_set(v___x_2702_, 3, v___x_2701_);
lean_ctor_set(v___x_2702_, 4, v___x_2701_);
return v___x_2702_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v___x_2703_, lean_object* v_declName_2704_, lean_object* v_majorPos_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_majorPos_2705_);
v___x_2710_ = 0;
v___x_2711_ = 1;
v___x_2712_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2715_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2717_ = lean_box(0);
lean_inc(v___x_2703_);
v___x_2718_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2718_, 0, v___x_2712_);
lean_ctor_set(v___x_2718_, 1, v___x_2703_);
lean_ctor_set(v___x_2718_, 2, v___x_2715_);
lean_ctor_set(v___x_2718_, 3, v___x_2716_);
lean_ctor_set(v___x_2718_, 4, v___x_2717_);
lean_ctor_set(v___x_2718_, 5, v___x_2713_);
lean_ctor_set(v___x_2718_, 6, v___x_2717_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7, v___x_2710_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7 + 1, v___x_2710_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7 + 2, v___x_2710_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7 + 3, v___x_2711_);
v___x_2719_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2720_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2721_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2719_);
lean_ctor_set(v___x_2722_, 1, v___x_2720_);
lean_ctor_set(v___x_2722_, 2, v___x_2703_);
lean_ctor_set(v___x_2722_, 3, v___x_2714_);
lean_ctor_set(v___x_2722_, 4, v___x_2721_);
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_st_mk_ref(v___x_2722_);
v___x_2725_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2704_, v___x_2709_, v___x_2718_, v___x_2724_, v___y_2706_, v___y_2707_);
lean_dec_ref_known(v___x_2718_, 7);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2733_; 
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v___x_2725_, 0);
lean_dec(v_unused_2734_);
v___x_2727_ = v___x_2725_;
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v___x_2725_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = lean_st_ref_get(v___x_2724_);
lean_dec(v___x_2724_);
lean_dec(v___x_2729_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2723_);
v___x_2731_ = v___x_2727_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2723_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
else
{
lean_dec(v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v___x_2725_, 0);
lean_dec(v_unused_2742_);
v___x_2736_ = v___x_2725_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_dec(v___x_2725_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2723_);
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2723_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_a_2743_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2725_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2725_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2703_ = stack[0].m_obj;
lean_object* v_declName_2704_ = stack[1].m_obj;
lean_object* v_majorPos_2705_ = stack[2].m_obj;
lean_object* v___y_2706_ = stack[3].m_obj;
lean_object* v___y_2707_ = stack[4].m_obj;
lean_object* v_res_2751_;
v_res_2751_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_2703_, v_declName_2704_, v_majorPos_2705_, v___y_2706_, v___y_2707_);
stack->m_obj
 = v_res_2751_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v___x_2752_, lean_object* v_declName_2753_, lean_object* v_majorPos_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_2752_, v_declName_2753_, v_majorPos_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
return v_res_2758_;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2785_ = l_Lean_registerParametricAttribute___redArg(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2786_;
v_res_2786_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2786_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object* v_env_2789_, lean_object* v_declName_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = l_Lean_Meta_recursorAttribute;
v___x_2793_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2791_, v___x_2792_, v_env_2789_, v_declName_2790_);
return v___x_2793_;
}
}
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object* v_declName_2794_, lean_object* v_majorPos_x3f_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_st_ref_get(v_a_2799_);
if (lean_obj_tag(v_majorPos_x3f_2795_) == 0)
{
lean_object* v_env_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_env_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_ref(v_env_2802_);
lean_dec(v___x_2801_);
lean_inc(v_declName_2794_);
v___x_2803_ = l_Lean_Meta_getMajorPos_x3f(v_env_2802_, v_declName_2794_);
v___x_2804_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2794_, v___x_2803_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; 
lean_dec(v___x_2801_);
v___x_2805_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2794_, v_majorPos_x3f_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
return v___x_2805_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkRecursorInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2794_ = stack[0].m_obj;
lean_object* v_majorPos_x3f_2795_ = stack[1].m_obj;
lean_object* v_a_2796_ = stack[2].m_obj;
lean_object* v_a_2797_ = stack[3].m_obj;
lean_object* v_a_2798_ = stack[4].m_obj;
lean_object* v_a_2799_ = stack[5].m_obj;
lean_object* v_res_2806_;
v_res_2806_ = l_Lean_Meta_mkRecursorInfo(v_declName_2794_, v_majorPos_x3f_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
stack->m_obj
 = v_res_2806_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo___boxed(lean_object* v_declName_2807_, lean_object* v_majorPos_x3f_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Meta_mkRecursorInfo(v_declName_2807_, v_majorPos_x3f_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
return v_res_2814_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_RecursorInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recursorAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recursorAttribute);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_RecursorInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_RecursorInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_RecursorInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_RecursorInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_RecursorInfo(builtin);
}
#ifdef __cplusplus
}
#endif
