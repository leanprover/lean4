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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 219, .m_capacity = 219, .m_length = 218, .m_data = "`, motive must have a type of the form (C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), (i : B A) is a (possibly empty) telescope (aka indices), and I is a constant"};
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
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
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "recursorAttribute"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 14, 117, 146, 218, 161, 149, 75)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 1, 161, 9, 253, 193, 133, 24)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "user defined recursor, numerical parameter specifies position of the major premise"};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recursorAttribute;
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_RecursorUnivLevelPos_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_idx_8_; lean_object* v___x_9_; 
v_idx_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_idx_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_idx_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_motive_elim___redArg(lean_object* v_t_22_, lean_object* v_motive_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_22_, v_motive_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_motive_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_motive_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_26_, v_motive_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_majorType_elim___redArg(lean_object* v_t_30_, lean_object* v_majorType_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_30_, v_majorType_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorUnivLevelPos_majorType_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_majorType_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_34_, v_majorType_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0(lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0));
return v___x_40_;
}
else
{
lean_object* v_idx_41_; lean_object* v___x_42_; 
v_idx_41_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_idx_41_);
lean_dec_ref(v_x_39_);
v___x_42_ = l_Nat_reprFast(v_idx_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object* v_info_45_){
_start:
{
lean_object* v_paramsPos_46_; lean_object* v___x_47_; 
v_paramsPos_46_ = lean_ctor_get(v_info_45_, 5);
v___x_47_ = l_List_lengthTR___redArg(v_paramsPos_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object* v_info_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Meta_RecursorInfo_numParams(v_info_48_);
lean_dec_ref(v_info_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object* v_info_50_){
_start:
{
lean_object* v_indicesPos_51_; lean_object* v___x_52_; 
v_indicesPos_51_ = lean_ctor_get(v_info_50_, 6);
v___x_52_ = l_List_lengthTR___redArg(v_indicesPos_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object* v_info_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_53_);
lean_dec_ref(v_info_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object* v_info_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_RecursorInfo_numParams(v_info_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object* v_info_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_RecursorInfo_motivePos(v_info_57_);
lean_dec_ref(v_info_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object* v_info_59_){
_start:
{
lean_object* v_majorPos_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_majorPos_60_ = lean_ctor_get(v_info_59_, 4);
v___x_61_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_59_);
v___x_62_ = lean_nat_sub(v_majorPos_60_, v___x_61_);
lean_dec(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object* v_info_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_63_);
lean_dec_ref(v_info_63_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object* v_info_65_, lean_object* v_pos_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; uint8_t v___y_70_; 
v___x_67_ = l_Lean_Meta_RecursorInfo_numParams(v_info_65_);
v___x_68_ = lean_nat_dec_le(v_pos_66_, v___x_67_);
lean_dec(v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_65_);
v___x_73_ = lean_nat_dec_le(v___x_72_, v_pos_66_);
lean_dec(v___x_72_);
if (v___x_73_ == 0)
{
v___y_70_ = v___x_73_;
goto v___jp_69_;
}
else
{
lean_object* v_majorPos_74_; uint8_t v___x_75_; 
v_majorPos_74_ = lean_ctor_get(v_info_65_, 4);
v___x_75_ = lean_nat_dec_le(v_pos_66_, v_majorPos_74_);
v___y_70_ = v___x_75_;
goto v___jp_69_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
v___jp_69_:
{
if (v___y_70_ == 0)
{
uint8_t v___x_71_; 
v___x_71_ = 1;
return v___x_71_;
}
else
{
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object* v_info_77_, lean_object* v_pos_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Meta_RecursorInfo_isMinor(v_info_77_, v_pos_78_);
lean_dec(v_pos_78_);
lean_dec_ref(v_info_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object* v_info_81_){
_start:
{
lean_object* v_numArgs_82_; lean_object* v_majorPos_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_r_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_numArgs_82_ = lean_ctor_get(v_info_81_, 3);
v_majorPos_83_ = lean_ctor_get(v_info_81_, 4);
v___x_84_ = l_Lean_Meta_RecursorInfo_numParams(v_info_81_);
v___x_85_ = lean_nat_sub(v_numArgs_82_, v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_unsigned_to_nat(1u);
v_r_87_ = lean_nat_sub(v___x_85_, v___x_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_nat_add(v_majorPos_83_, v___x_86_);
v___x_89_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_81_);
v___x_90_ = lean_nat_sub(v___x_88_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_nat_sub(v_r_87_, v___x_90_);
lean_dec(v___x_90_);
lean_dec(v_r_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object* v_info_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_RecursorInfo_numMinors(v_info_92_);
lean_dec_ref(v_info_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString___lam__0(lean_object* v___f_112_, lean_object* v___f_113_, lean_object* v___f_114_, lean_object* v___f_115_, lean_object* v_info_116_){
_start:
{
lean_object* v_recursorName_117_; lean_object* v_typeName_118_; lean_object* v_univLevelPos_119_; uint8_t v_depElim_120_; uint8_t v_recursive_121_; lean_object* v_numArgs_122_; lean_object* v_majorPos_123_; lean_object* v_paramsPos_124_; lean_object* v_indicesPos_125_; lean_object* v_produceMotive_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___y_200_; 
v_recursorName_117_ = lean_ctor_get(v_info_116_, 0);
v_typeName_118_ = lean_ctor_get(v_info_116_, 1);
v_univLevelPos_119_ = lean_ctor_get(v_info_116_, 2);
v_depElim_120_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*8);
v_recursive_121_ = lean_ctor_get_uint8(v_info_116_, sizeof(void*)*8 + 1);
v_numArgs_122_ = lean_ctor_get(v_info_116_, 3);
v_majorPos_123_ = lean_ctor_get(v_info_116_, 4);
lean_inc(v_majorPos_123_);
v_paramsPos_124_ = lean_ctor_get(v_info_116_, 5);
lean_inc(v_paramsPos_124_);
v_indicesPos_125_ = lean_ctor_get(v_info_116_, 6);
lean_inc(v_indicesPos_125_);
v_produceMotive_126_ = lean_ctor_get(v_info_116_, 7);
lean_inc(v_produceMotive_126_);
v___x_127_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0));
v___x_128_ = 1;
lean_inc(v_recursorName_117_);
v___x_129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_recursorName_117_, v___x_128_);
v___x_130_ = lean_string_append(v___x_127_, v___x_129_);
lean_dec_ref(v___x_129_);
v___x_131_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1));
v___x_186_ = lean_string_append(v___x_130_, v___x_131_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12));
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
lean_inc(v_typeName_118_);
v___x_189_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_typeName_118_, v___x_128_);
v___x_190_ = lean_string_append(v___x_188_, v___x_189_);
lean_dec_ref(v___x_189_);
v___x_191_ = lean_string_append(v___x_190_, v___x_131_);
v___x_192_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13));
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
lean_inc(v_univLevelPos_119_);
v___x_194_ = l_List_toString___redArg(v___f_115_, v_univLevelPos_119_);
v___x_195_ = lean_string_append(v___x_193_, v___x_194_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_string_append(v___x_195_, v___x_131_);
v___x_197_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
if (v_depElim_120_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16));
v___y_200_ = v___x_207_;
goto v___jp_199_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17));
v___y_200_ = v___x_208_;
goto v___jp_199_;
}
v___jp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_135_ = lean_string_append(v___y_133_, v___y_134_);
v___x_136_ = lean_string_append(v___x_135_, v___x_131_);
v___x_137_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2));
v___x_138_ = lean_string_append(v___x_136_, v___x_137_);
lean_inc(v_numArgs_122_);
v___x_139_ = l_Nat_reprFast(v_numArgs_122_);
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
lean_dec_ref(v___x_139_);
v___x_141_ = lean_string_append(v___x_140_, v___x_131_);
v___x_142_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3));
v___x_143_ = lean_string_append(v___x_141_, v___x_142_);
v___x_144_ = l_Lean_Meta_RecursorInfo_numParams(v_info_116_);
v___x_145_ = l_Nat_reprFast(v___x_144_);
v___x_146_ = lean_string_append(v___x_143_, v___x_145_);
v___x_147_ = lean_string_append(v___x_146_, v___x_131_);
v___x_148_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4));
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
v___x_150_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_116_);
v___x_151_ = l_Nat_reprFast(v___x_150_);
v___x_152_ = lean_string_append(v___x_149_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = lean_string_append(v___x_152_, v___x_131_);
v___x_154_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5));
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
v___x_156_ = l_Lean_Meta_RecursorInfo_numMinors(v_info_116_);
lean_dec_ref(v_info_116_);
v___x_157_ = l_Nat_reprFast(v___x_156_);
v___x_158_ = lean_string_append(v___x_155_, v___x_157_);
lean_dec_ref(v___x_157_);
v___x_159_ = lean_string_append(v___x_158_, v___x_131_);
v___x_160_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6));
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
v___x_162_ = l_Nat_reprFast(v_majorPos_123_);
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
lean_dec_ref(v___x_162_);
v___x_164_ = lean_string_append(v___x_163_, v___x_131_);
v___x_165_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7));
v___x_166_ = lean_string_append(v___x_164_, v___x_165_);
v___x_167_ = lean_string_append(v___x_166_, v___x_145_);
lean_dec_ref(v___x_145_);
v___x_168_ = lean_string_append(v___x_167_, v___x_131_);
v___x_169_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8));
v___x_170_ = lean_string_append(v___x_168_, v___x_169_);
v___x_171_ = l_List_toString___redArg(v___f_112_, v_paramsPos_124_);
v___x_172_ = lean_string_append(v___x_170_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_173_ = lean_string_append(v___x_172_, v___x_131_);
v___x_174_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9));
v___x_175_ = lean_string_append(v___x_173_, v___x_174_);
v___x_176_ = l_List_toString___redArg(v___f_113_, v_indicesPos_125_);
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = lean_string_append(v___x_177_, v___x_131_);
v___x_179_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10));
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
v___x_181_ = l_List_toString___redArg(v___f_114_, v_produceMotive_126_);
v___x_182_ = lean_string_append(v___x_180_, v___x_181_);
lean_dec_ref(v___x_181_);
v___x_183_ = lean_string_append(v___x_182_, v___x_131_);
v___x_184_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11));
v___x_185_ = lean_string_append(v___x_183_, v___x_184_);
return v___x_185_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = lean_string_append(v___x_198_, v___y_200_);
v___x_202_ = lean_string_append(v___x_201_, v___x_131_);
v___x_203_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15));
v___x_204_ = lean_string_append(v___x_202_, v___x_203_);
if (v_recursive_121_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16));
v___y_133_ = v___x_204_;
v___y_134_ = v___x_205_;
goto v___jp_132_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17));
v___y_133_ = v___x_204_;
v___y_134_ = v___x_206_;
goto v___jp_132_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_instMonadEIO(lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_toApplicative_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_293_; 
v___x_230_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0);
v___x_231_ = l_StateRefT_x27_instMonad___redArg(v___x_230_);
v_toApplicative_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v___x_231_, 1);
lean_dec(v_unused_294_);
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_293_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_toApplicative_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_293_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_toFunctor_236_; lean_object* v_toSeq_237_; lean_object* v_toSeqLeft_238_; lean_object* v_toSeqRight_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_291_; 
v_toFunctor_236_ = lean_ctor_get(v_toApplicative_232_, 0);
v_toSeq_237_ = lean_ctor_get(v_toApplicative_232_, 2);
v_toSeqLeft_238_ = lean_ctor_get(v_toApplicative_232_, 3);
v_toSeqRight_239_ = lean_ctor_get(v_toApplicative_232_, 4);
v_isSharedCheck_291_ = !lean_is_exclusive(v_toApplicative_232_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v_toApplicative_232_, 1);
lean_dec(v_unused_292_);
v___x_241_ = v_toApplicative_232_;
v_isShared_242_ = v_isSharedCheck_291_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_toSeqRight_239_);
lean_inc(v_toSeqLeft_238_);
lean_inc(v_toSeq_237_);
lean_inc(v_toFunctor_236_);
lean_dec(v_toApplicative_232_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_291_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_252_; 
v___f_243_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1));
v___f_244_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_236_);
v___f_245_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_245_, 0, v_toFunctor_236_);
v___f_246_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_246_, 0, v_toFunctor_236_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___f_245_);
lean_ctor_set(v___x_247_, 1, v___f_246_);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_248_, 0, v_toSeqRight_239_);
v___f_249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_249_, 0, v_toSeqLeft_238_);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_250_, 0, v_toSeq_237_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 4, v___f_248_);
lean_ctor_set(v___x_241_, 3, v___f_249_);
lean_ctor_set(v___x_241_, 2, v___f_250_);
lean_ctor_set(v___x_241_, 1, v___f_243_);
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_252_ = v___x_241_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___f_243_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___f_250_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v___f_249_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v___f_248_);
v___x_252_ = v_reuseFailAlloc_290_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___f_244_);
lean_ctor_set(v___x_234_, 0, v___x_252_);
v___x_254_ = v___x_234_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___f_244_);
v___x_254_ = v_reuseFailAlloc_289_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v_toApplicative_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_287_; 
v___x_255_ = l_StateRefT_x27_instMonad___redArg(v___x_254_);
v_toApplicative_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_255_, 1);
lean_dec(v_unused_288_);
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_287_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_toApplicative_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_287_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_toFunctor_260_; lean_object* v_toSeq_261_; lean_object* v_toSeqLeft_262_; lean_object* v_toSeqRight_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_285_; 
v_toFunctor_260_ = lean_ctor_get(v_toApplicative_256_, 0);
v_toSeq_261_ = lean_ctor_get(v_toApplicative_256_, 2);
v_toSeqLeft_262_ = lean_ctor_get(v_toApplicative_256_, 3);
v_toSeqRight_263_ = lean_ctor_get(v_toApplicative_256_, 4);
v_isSharedCheck_285_ = !lean_is_exclusive(v_toApplicative_256_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_toApplicative_256_, 1);
lean_dec(v_unused_286_);
v___x_265_ = v_toApplicative_256_;
v_isShared_266_ = v_isSharedCheck_285_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_toSeqRight_263_);
lean_inc(v_toSeqLeft_262_);
lean_inc(v_toSeq_261_);
lean_inc(v_toFunctor_260_);
lean_dec(v_toApplicative_256_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_285_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___x_276_; 
v___f_267_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3));
v___f_268_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_260_);
v___f_269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_269_, 0, v_toFunctor_260_);
v___f_270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_270_, 0, v_toFunctor_260_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___f_269_);
lean_ctor_set(v___x_271_, 1, v___f_270_);
v___f_272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_272_, 0, v_toSeqRight_263_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_273_, 0, v_toSeqLeft_262_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_274_, 0, v_toSeq_261_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 4, v___f_272_);
lean_ctor_set(v___x_265_, 3, v___f_273_);
lean_ctor_set(v___x_265_, 2, v___f_274_);
lean_ctor_set(v___x_265_, 1, v___f_267_);
lean_ctor_set(v___x_265_, 0, v___x_271_);
v___x_276_ = v___x_265_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___f_267_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v___f_274_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v___f_273_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v___f_272_);
v___x_276_ = v_reuseFailAlloc_284_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___f_268_);
lean_ctor_set(v___x_258_, 0, v___x_276_);
v___x_278_ = v___x_258_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___f_268_);
v___x_278_ = v_reuseFailAlloc_283_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_3473__overap_281_; lean_object* v___x_282_; 
v___x_279_ = lean_box(0);
v___x_280_ = l_instInhabitedOfMonad___redArg(v___x_278_, v___x_279_);
v___x_3473__overap_281_ = lean_panic_fn_borrowed(v___x_280_, v_msg_224_);
lean_dec(v___x_280_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
v___x_282_ = lean_apply_5(v___x_3473__overap_281_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, lean_box(0));
return v___x_282_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___boxed(lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(lean_object* v_msgData_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v_env_309_; lean_object* v___x_310_; lean_object* v_mctx_311_; lean_object* v_lctx_312_; lean_object* v_options_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_308_ = lean_st_ref_get(v___y_306_);
v_env_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_env_309_);
lean_dec(v___x_308_);
v___x_310_ = lean_st_ref_get(v___y_304_);
v_mctx_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_mctx_311_);
lean_dec(v___x_310_);
v_lctx_312_ = lean_ctor_get(v___y_303_, 2);
v_options_313_ = lean_ctor_get(v___y_305_, 2);
lean_inc_ref(v_options_313_);
lean_inc_ref(v_lctx_312_);
v___x_314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_314_, 0, v_env_309_);
lean_ctor_set(v___x_314_, 1, v_mctx_311_);
lean_ctor_set(v___x_314_, 2, v_lctx_312_);
lean_ctor_set(v___x_314_, 3, v_options_313_);
v___x_315_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_msgData_302_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msgData_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_ref_330_ = lean_ctor_get(v___y_327_, 5);
v___x_331_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v_ref_330_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_ref_330_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 1);
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_357_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6));
v___x_358_ = lean_unsigned_to_nat(11u);
v___x_359_ = lean_unsigned_to_nat(129u);
v___x_360_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5));
v___x_361_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4));
v___x_362_ = l_mkPanicMessageWithDecl(v___x_361_, v___x_360_, v___x_359_, v___x_358_, v___x_357_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(lean_object* v_constName_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_377_; lean_object* v_env_378_; uint8_t v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_st_ref_get(v___y_367_);
v_env_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_env_378_);
lean_dec(v___x_377_);
v___x_379_ = 0;
lean_inc(v_constName_363_);
v___x_380_ = l_Lean_Environment_findAsync_x3f(v_env_378_, v_constName_363_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 1)
{
lean_object* v_val_381_; uint8_t v_kind_382_; 
v_val_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_val_381_);
lean_dec_ref(v___x_380_);
v_kind_382_ = lean_ctor_get_uint8(v_val_381_, sizeof(void*)*3);
if (v_kind_382_ == 7)
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_381_);
if (lean_obj_tag(v___x_383_) == 7)
{
lean_object* v_val_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_constName_363_);
v_val_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_val_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 0);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_val_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v___x_383_);
v___x_392_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7);
v___x_393_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v___x_392_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
if (lean_obj_tag(v_a_394_) == 0)
{
lean_del_object(v___x_396_);
goto v___jp_369_;
}
else
{
lean_object* v_val_398_; lean_object* v___x_400_; 
lean_dec(v_constName_363_);
v_val_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_val_398_);
lean_dec_ref(v_a_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_val_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_val_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_constName_363_);
v_a_403_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_dec(v_val_381_);
goto v___jp_369_;
}
}
else
{
lean_dec(v___x_380_);
goto v___jp_369_;
}
v___jp_369_:
{
lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_371_ = 0;
v___x_372_ = l_Lean_MessageData_ofConstName(v_constName_363_, v___x_371_);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_370_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_375_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___boxed(lean_object* v_constName_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v_constName_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(lean_object* v_declName_418_, lean_object* v_majorPos_x3f_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___y_426_; lean_object* v___y_427_; 
if (lean_obj_tag(v_majorPos_x3f_419_) == 0)
{
lean_object* v___x_431_; lean_object* v_env_432_; uint8_t v___x_433_; 
v___x_431_ = lean_st_ref_get(v_a_423_);
v_env_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_432_);
lean_dec(v___x_431_);
lean_inc(v_declName_418_);
v___x_433_ = l_Lean_isAuxRecursor(v_env_432_, v_declName_418_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec(v_declName_418_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_majorPos_x3f_419_);
return v___x_434_;
}
else
{
if (lean_obj_tag(v_declName_418_) == 1)
{
lean_object* v_pre_435_; lean_object* v_str_436_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_pre_435_ = lean_ctor_get(v_declName_418_, 0);
lean_inc(v_pre_435_);
v_str_436_ = lean_ctor_get(v_declName_418_, 1);
lean_inc_ref(v_str_436_);
lean_dec_ref(v_declName_418_);
v___x_456_ = l_Lean_recOnSuffix;
v___x_457_ = lean_string_dec_eq(v_str_436_, v___x_456_);
if (v___x_457_ == 0)
{
if (v___x_433_ == 0)
{
goto v___jp_437_;
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = l_Lean_casesOnSuffix;
v___x_459_ = lean_string_dec_eq(v_str_436_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = l_Lean_brecOnSuffix;
v___x_461_ = lean_string_dec_eq(v_str_436_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec_ref(v_str_436_);
lean_dec(v_pre_435_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_majorPos_x3f_419_);
return v___x_462_;
}
else
{
goto v___jp_437_;
}
}
else
{
goto v___jp_437_;
}
}
}
else
{
goto v___jp_437_;
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = l_Lean_mkRecName(v_pre_435_);
v___x_439_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v___x_438_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_numParams_441_; lean_object* v_numIndices_442_; lean_object* v_numMotives_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___x_439_);
v_numParams_441_ = lean_ctor_get(v_a_440_, 2);
lean_inc(v_numParams_441_);
v_numIndices_442_ = lean_ctor_get(v_a_440_, 3);
lean_inc(v_numIndices_442_);
v_numMotives_443_ = lean_ctor_get(v_a_440_, 4);
lean_inc(v_numMotives_443_);
lean_dec(v_a_440_);
v___x_444_ = lean_nat_add(v_numParams_441_, v_numIndices_442_);
lean_dec(v_numIndices_442_);
lean_dec(v_numParams_441_);
v___x_445_ = l_Lean_casesOnSuffix;
v___x_446_ = lean_string_dec_eq(v_str_436_, v___x_445_);
lean_dec_ref(v_str_436_);
if (v___x_446_ == 0)
{
v___y_426_ = v___x_444_;
v___y_427_ = v_numMotives_443_;
goto v___jp_425_;
}
else
{
lean_object* v___x_447_; 
lean_dec(v_numMotives_443_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___y_426_ = v___x_444_;
v___y_427_ = v___x_447_;
goto v___jp_425_;
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v_str_436_);
v_a_448_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_439_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v_declName_418_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_majorPos_x3f_419_);
return v___x_463_;
}
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_declName_418_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_majorPos_x3f_419_);
return v___x_464_;
}
v___jp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_nat_add(v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___boxed(lean_object* v_declName_465_, lean_object* v_majorPos_x3f_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_465_, v_majorPos_x3f_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(lean_object* v_00_u03b1_473_, lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_481_, lean_object* v_msg_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(v_00_u03b1_481_, v_msg_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_488_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(uint8_t v___x_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; uint8_t v___y_496_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_494_ = 1;
v___x_500_ = lean_array_uget_borrowed(v_as_490_, v_i_491_);
v___x_501_ = l_Lean_Expr_isFVar(v___x_500_);
if (v___x_501_ == 0)
{
v___y_496_ = v___x_489_;
goto v___jp_495_;
}
else
{
v___y_496_ = v___x_493_;
goto v___jp_495_;
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
size_t v___x_497_; size_t v___x_498_; 
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_491_, v___x_497_);
v_i_491_ = v___x_498_;
goto _start;
}
else
{
return v___x_494_;
}
}
}
else
{
uint8_t v___x_502_; 
v___x_502_ = 0;
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0___boxed(lean_object* v___x_503_, lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_){
_start:
{
uint8_t v___x_579__boxed_507_; size_t v_i_boxed_508_; size_t v_stop_boxed_509_; uint8_t v_res_510_; lean_object* v_r_511_; 
v___x_579__boxed_507_ = lean_unbox(v___x_503_);
v_i_boxed_508_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_509_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_579__boxed_507_, v_as_504_, v_i_boxed_508_, v_stop_boxed_509_);
lean_dec_ref(v_as_504_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(lean_object* v_declName_518_, lean_object* v_motive_519_, lean_object* v_motiveArgs_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
uint8_t v___y_527_; uint8_t v___y_535_; uint8_t v___x_538_; 
v___x_538_ = l_Lean_Expr_isFVar(v_motive_519_);
if (v___x_538_ == 0)
{
v___y_535_ = v___x_538_;
goto v___jp_534_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_array_get_size(v_motiveArgs_520_);
v___x_541_ = lean_nat_dec_lt(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
v___y_535_ = v___x_538_;
goto v___jp_534_;
}
else
{
if (v___x_541_ == 0)
{
v___y_535_ = v___x_538_;
goto v___jp_534_;
}
else
{
size_t v___x_542_; size_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_540_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_538_, v_motiveArgs_520_, v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
v___y_535_ = v___x_538_;
goto v___jp_534_;
}
else
{
uint8_t v___x_545_; 
v___x_545_ = 0;
v___y_527_ = v___x_545_;
goto v___jp_526_;
}
}
}
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_529_ = l_Lean_MessageData_ofConstName(v_declName_518_, v___y_527_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_532_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
return v___x_533_;
}
v___jp_534_:
{
if (v___y_535_ == 0)
{
v___y_527_ = v___y_535_;
goto v___jp_526_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_declName_518_);
v___x_536_ = lean_box(0);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(lean_object* v_declName_546_, lean_object* v_motive_547_, lean_object* v_motiveArgs_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_546_, v_motive_547_, v_motiveArgs_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec_ref(v_motiveArgs_548_);
lean_dec_ref(v_motive_547_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(lean_object* v_xs_555_, lean_object* v_motive_556_, lean_object* v_i_557_){
_start:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_array_get_size(v_xs_555_);
v___x_559_ = lean_nat_dec_lt(v_i_557_, v___x_558_);
if (v___x_559_ == 0)
{
return v_i_557_;
}
else
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_fget_borrowed(v_xs_555_, v_i_557_);
v___x_561_ = lean_expr_eqv(v_motive_556_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_i_557_, v___x_562_);
lean_dec(v_i_557_);
v_i_557_ = v___x_563_;
goto _start;
}
else
{
return v_i_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(lean_object* v_xs_565_, lean_object* v_motive_566_, lean_object* v_i_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(v_xs_565_, v_motive_566_, v_i_567_);
lean_dec_ref(v_motive_566_);
lean_dec_ref(v_xs_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(lean_object* v_xs_569_, lean_object* v_v_570_, lean_object* v_i_571_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_get_size(v_xs_569_);
v___x_573_ = lean_nat_dec_lt(v_i_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v_i_571_);
v___x_574_ = lean_box(0);
return v___x_574_;
}
else
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_array_fget_borrowed(v_xs_569_, v_i_571_);
v___x_576_ = lean_expr_eqv(v___x_575_, v_v_570_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_i_571_, v___x_577_);
lean_dec(v_i_571_);
v_i_571_ = v___x_578_;
goto _start;
}
else
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_i_571_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_581_, lean_object* v_v_582_, lean_object* v_i_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_581_, v_v_582_, v_i_583_);
lean_dec_ref(v_v_582_);
lean_dec_ref(v_xs_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(lean_object* v_xs_585_, lean_object* v_v_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_585_, v_v_586_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0___boxed(lean_object* v_xs_589_, lean_object* v_v_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_589_, v_v_590_);
lean_dec_ref(v_v_590_);
lean_dec_ref(v_xs_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(lean_object* v_xs_592_, lean_object* v_v_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_592_, v_v_593_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_box(0);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_val_596_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_val_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0___boxed(lean_object* v_xs_604_, lean_object* v_v_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_604_, v_v_605_);
lean_dec_ref(v_v_605_);
lean_dec_ref(v_xs_604_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(lean_object* v_a_607_, lean_object* v_as_608_, size_t v_i_609_, size_t v_stop_610_){
_start:
{
uint8_t v___x_611_; 
v___x_611_ = lean_usize_dec_eq(v_i_609_, v_stop_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_uget_borrowed(v_as_608_, v_i_609_);
v___x_613_ = lean_expr_eqv(v_a_607_, v___x_612_);
if (v___x_613_ == 0)
{
size_t v___x_614_; size_t v___x_615_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_609_, v___x_614_);
v_i_609_ = v___x_615_;
goto _start;
}
else
{
return v___x_613_;
}
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2___boxed(lean_object* v_a_618_, lean_object* v_as_619_, lean_object* v_i_620_, lean_object* v_stop_621_){
_start:
{
size_t v_i_boxed_622_; size_t v_stop_boxed_623_; uint8_t v_res_624_; lean_object* v_r_625_; 
v_i_boxed_622_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_stop_boxed_623_ = lean_unbox_usize(v_stop_621_);
lean_dec(v_stop_621_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_618_, v_as_619_, v_i_boxed_622_, v_stop_boxed_623_);
lean_dec_ref(v_as_619_);
lean_dec_ref(v_a_618_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(lean_object* v_as_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_array_get_size(v_as_626_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
size_t v___x_631_; size_t v___x_632_; uint8_t v___x_633_; 
v___x_631_ = ((size_t)0ULL);
v___x_632_ = lean_usize_of_nat(v___x_629_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_627_, v_as_626_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1___boxed(lean_object* v_as_634_, lean_object* v_a_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_as_634_, v_a_635_);
lean_dec_ref(v_a_635_);
lean_dec_ref(v_as_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(lean_object* v_declName_653_, lean_object* v_majorPos_x3f_654_, lean_object* v_xs_655_, lean_object* v_motiveArgs_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
if (lean_obj_tag(v_majorPos_x3f_654_) == 0)
{
lean_object* v___x_662_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_662_ = l_Lean_instInhabitedExpr;
v___x_692_ = lean_array_get_size(v_motiveArgs_656_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
v___y_664_ = v_a_657_;
v___y_665_ = v_a_658_;
v___y_666_ = v_a_659_;
v___y_667_ = v_a_660_;
goto v___jp_663_;
}
else
{
lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v___x_695_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3);
v___x_696_ = 0;
v___x_697_ = l_Lean_MessageData_ofConstName(v_declName_653_, v___x_696_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_695_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_700_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
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
v___jp_663_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_major_671_; lean_object* v___x_672_; 
v___x_668_ = lean_array_get_size(v_motiveArgs_656_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_sub(v___x_668_, v___x_669_);
v_major_671_ = lean_array_get_borrowed(v___x_662_, v_motiveArgs_656_, v___x_670_);
lean_dec(v___x_670_);
v___x_672_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_655_, v_major_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_673_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1);
v___x_674_ = 0;
v___x_675_ = l_Lean_MessageData_ofConstName(v_declName_653_, v___x_674_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_678_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
return v___x_679_;
}
else
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_declName_653_);
v_val_680_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_691_ == 0)
{
v___x_682_ = v___x_672_;
v_isShared_683_ = v_isSharedCheck_691_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v___x_672_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_691_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_684_ = 1;
v___x_685_ = lean_box(v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_val_680_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
lean_inc(v_major_671_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_major_671_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
lean_ctor_set(v___x_682_, 0, v___x_687_);
v___x_689_ = v___x_682_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_declName_653_);
v_val_710_ = lean_ctor_get(v_majorPos_x3f_654_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_majorPos_x3f_654_);
if (v_isSharedCheck_734_ == 0)
{
v___x_712_ = v_majorPos_x3f_654_;
v_isShared_713_ = v_isSharedCheck_734_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v_majorPos_x3f_654_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_734_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_array_get_size(v_xs_655_);
v___x_715_ = lean_nat_dec_lt(v_val_710_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
lean_dec(v_val_710_);
v___x_716_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7);
v___x_717_ = l_Nat_reprFast(v___x_714_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 3);
lean_ctor_set(v___x_712_, 0, v___x_717_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_725_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_720_ = l_Lean_MessageData_ofFormat(v___x_719_);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_716_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_723_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
return v___x_724_;
}
}
else
{
lean_object* v_major_726_; uint8_t v_depElim_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v_major_726_ = lean_array_fget_borrowed(v_xs_655_, v_val_710_);
v_depElim_727_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_motiveArgs_656_, v_major_726_);
v___x_728_ = lean_box(v_depElim_727_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_val_710_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_inc(v_major_726_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_major_726_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 0);
lean_ctor_set(v___x_712_, 0, v___x_730_);
v___x_732_ = v___x_712_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(lean_object* v_declName_735_, lean_object* v_majorPos_x3f_736_, lean_object* v_xs_737_, lean_object* v_motiveArgs_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_735_, v_majorPos_x3f_736_, v_xs_737_, v_motiveArgs_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec_ref(v_motiveArgs_738_);
lean_dec_ref(v_xs_737_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(lean_object* v___x_745_, lean_object* v_as_746_, size_t v_sz_747_, size_t v_i_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_748_, v_sz_747_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_dec_ref(v___x_745_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_b_749_);
return v___x_756_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_758_; 
v_a_757_ = lean_array_uget_borrowed(v_as_746_, v_i_748_);
lean_inc_ref(v___x_745_);
lean_inc(v_a_757_);
v___x_758_ = l_Lean_Meta_isExprDefEq(v_a_757_, v___x_745_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_793_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_793_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_793_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_793_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_unbox(v_a_759_);
lean_dec(v_a_759_);
if (v___x_763_ == 0)
{
lean_object* v_snd_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_761_);
v_snd_764_ = lean_ctor_get(v_b_749_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_b_749_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v_b_749_, 0);
lean_dec(v_unused_778_);
v___x_766_ = v_b_749_;
v_isShared_767_ = v_isSharedCheck_777_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snd_764_);
lean_dec(v_b_749_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_777_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_snd_764_, v___x_769_);
lean_dec(v_snd_764_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_770_);
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_772_ = v___x_766_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
size_t v___x_773_; size_t v___x_774_; 
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_748_, v___x_773_);
v_i_748_ = v___x_774_;
v_b_749_ = v___x_772_;
goto _start;
}
}
}
else
{
lean_object* v_snd_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v___x_745_);
v_snd_779_ = lean_ctor_get(v_b_749_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_b_749_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_b_749_, 0);
lean_dec(v_unused_792_);
v___x_781_ = v_b_749_;
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_snd_779_);
lean_dec(v_b_749_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
lean_inc(v_snd_779_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v_snd_779_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_snd_779_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_786_);
v___x_788_ = v___x_761_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_b_749_);
lean_dec_ref(v___x_745_);
v_a_794_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_758_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_758_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0___boxed(lean_object* v___x_802_, lean_object* v_as_803_, lean_object* v_sz_804_, lean_object* v_i_805_, lean_object* v_b_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
size_t v_sz_boxed_812_; size_t v_i_boxed_813_; lean_object* v_res_814_; 
v_sz_boxed_812_ = lean_unbox_usize(v_sz_804_);
lean_dec(v_sz_804_);
v_i_boxed_813_ = lean_unbox_usize(v_i_805_);
lean_dec(v_i_805_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_802_, v_as_803_, v_sz_boxed_812_, v_i_boxed_813_, v_b_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec_ref(v_as_803_);
return v_res_814_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(lean_object* v_upperBound_821_, lean_object* v_xs_822_, lean_object* v_declName_823_, lean_object* v_Iargs_824_, lean_object* v_a_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_a_833_; uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_lt(v_a_825_, v_upperBound_821_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec(v_a_825_);
lean_dec(v_declName_823_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v_b_826_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_a_842_; lean_object* v___x_871_; lean_object* v___x_872_; size_t v_sz_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_839_ = l_Lean_instInhabitedExpr;
v___x_840_ = lean_array_get_borrowed(v___x_839_, v_xs_822_, v_a_825_);
v___x_871_ = lean_box(0);
v___x_872_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2));
v_sz_873_ = lean_array_size(v_Iargs_824_);
v___x_874_ = ((size_t)0ULL);
lean_inc(v___x_840_);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_840_, v_Iargs_824_, v_sz_873_, v___x_874_, v___x_872_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v_fst_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v_fst_877_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_fst_877_);
lean_dec(v_a_876_);
if (lean_obj_tag(v_fst_877_) == 0)
{
v_a_842_ = v___x_871_;
goto v___jp_841_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref(v_fst_877_);
if (lean_obj_tag(v_val_878_) == 0)
{
v_a_842_ = v_val_878_;
goto v___jp_841_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = lean_array_push(v_b_826_, v_val_878_);
v_a_833_ = v___x_879_;
goto v___jp_832_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v_b_826_);
lean_dec(v_a_825_);
lean_dec(v_declName_823_);
v_a_880_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_875_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = l_Lean_Expr_fvarId_x21(v___x_840_);
v___x_844_ = l_Lean_FVarId_getDecl___redArg(v___x_843_, v___y_827_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; uint8_t v___x_846_; uint8_t v___x_847_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_844_);
v___x_846_ = l_Lean_LocalDecl_binderInfo(v_a_845_);
lean_dec(v_a_845_);
v___x_847_ = l_Lean_BinderInfo_isInstImplicit(v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_a_842_);
v___x_848_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
lean_inc(v_declName_823_);
v___x_849_ = l_Lean_MessageData_ofConstName(v_declName_823_, v___x_847_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_852_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_dec_ref(v___x_853_);
v_a_833_ = v_b_826_;
goto v___jp_832_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v_b_826_);
lean_dec(v_a_825_);
lean_dec(v_declName_823_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_array_push(v_b_826_, v_a_842_);
v_a_833_ = v___x_862_;
goto v___jp_832_;
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_a_842_);
lean_dec_ref(v_b_826_);
lean_dec(v_a_825_);
lean_dec(v_declName_823_);
v_a_863_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_844_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_844_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(1u);
v___x_835_ = lean_nat_add(v_a_825_, v___x_834_);
lean_dec(v_a_825_);
v_a_825_ = v___x_835_;
v_b_826_ = v_a_833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___boxed(lean_object* v_upperBound_888_, lean_object* v_xs_889_, lean_object* v_declName_890_, lean_object* v_Iargs_891_, lean_object* v_a_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_888_, v_xs_889_, v_declName_890_, v_Iargs_891_, v_a_892_, v_b_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_Iargs_891_);
lean_dec_ref(v_xs_889_);
lean_dec(v_upperBound_888_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(lean_object* v_declName_902_, lean_object* v_xs_903_, lean_object* v_numParams_904_, lean_object* v_Iargs_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_paramsPos_912_; lean_object* v___x_913_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v_paramsPos_912_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0));
v___x_913_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_numParams_904_, v_xs_903_, v_declName_902_, v_Iargs_905_, v___x_911_, v_paramsPos_912_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_array_to_list(v_a_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_913_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(lean_object* v_declName_931_, lean_object* v_xs_932_, lean_object* v_numParams_933_, lean_object* v_Iargs_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_931_, v_xs_932_, v_numParams_933_, v_Iargs_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec_ref(v_Iargs_934_);
lean_dec(v_numParams_933_);
lean_dec_ref(v_xs_932_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(lean_object* v_upperBound_941_, lean_object* v_xs_942_, lean_object* v_declName_943_, lean_object* v_Iargs_944_, lean_object* v_inst_945_, lean_object* v_R_946_, lean_object* v_a_947_, lean_object* v_b_948_, lean_object* v_c_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_941_, v_xs_942_, v_declName_943_, v_Iargs_944_, v_a_947_, v_b_948_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___boxed(lean_object* v_upperBound_956_, lean_object* v_xs_957_, lean_object* v_declName_958_, lean_object* v_Iargs_959_, lean_object* v_inst_960_, lean_object* v_R_961_, lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v_c_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(v_upperBound_956_, v_xs_957_, v_declName_958_, v_Iargs_959_, v_inst_960_, v_R_961_, v_a_962_, v_b_963_, v_c_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v_Iargs_959_);
lean_dec_ref(v_xs_957_);
lean_dec(v_upperBound_956_);
return v_res_970_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(lean_object* v_declName_974_, lean_object* v_upperBound_975_, lean_object* v_majorPos_976_, lean_object* v_numIndices_977_, lean_object* v_xs_978_, lean_object* v_Iargs_979_, lean_object* v_a_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_a_988_; uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_lt(v_a_980_, v_upperBound_975_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec(v_a_980_);
lean_dec(v_declName_974_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_b_981_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; size_t v_sz_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1010_ = l_Lean_instInhabitedExpr;
v___x_1011_ = lean_nat_sub(v_majorPos_976_, v_numIndices_977_);
v___x_1012_ = lean_nat_add(v___x_1011_, v_a_980_);
lean_dec(v___x_1011_);
v___x_1013_ = lean_array_get_borrowed(v___x_1010_, v_xs_978_, v___x_1012_);
lean_dec(v___x_1012_);
v___x_1014_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2));
v_sz_1015_ = lean_array_size(v_Iargs_979_);
v___x_1016_ = ((size_t)0ULL);
lean_inc(v___x_1013_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_1013_, v_Iargs_979_, v_sz_1015_, v___x_1016_, v___x_1014_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v_fst_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v_fst_1019_ = lean_ctor_get(v_a_1018_, 0);
lean_inc(v_fst_1019_);
lean_dec(v_a_1018_);
if (lean_obj_tag(v_fst_1019_) == 0)
{
goto v___jp_992_;
}
else
{
lean_object* v_val_1020_; 
v_val_1020_ = lean_ctor_get(v_fst_1019_, 0);
lean_inc(v_val_1020_);
lean_dec_ref(v_fst_1019_);
if (lean_obj_tag(v_val_1020_) == 0)
{
goto v___jp_992_;
}
else
{
lean_object* v_val_1021_; lean_object* v___x_1022_; 
v_val_1021_ = lean_ctor_get(v_val_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref(v_val_1020_);
v___x_1022_ = lean_array_push(v_b_981_, v_val_1021_);
v_a_988_ = v___x_1022_;
goto v___jp_987_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_b_981_);
lean_dec(v_a_980_);
lean_dec(v_declName_974_);
v_a_1023_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1017_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
v___jp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_add(v_a_980_, v___x_989_);
lean_dec(v_a_980_);
v_a_980_ = v___x_990_;
v_b_981_ = v_a_988_;
goto _start;
}
v___jp_992_:
{
lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_993_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_994_ = 0;
lean_inc(v_declName_974_);
v___x_995_ = l_Lean_MessageData_ofConstName(v_declName_974_, v___x_994_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_993_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_998_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_dec_ref(v___x_999_);
v_a_988_ = v_b_981_;
goto v___jp_987_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_b_981_);
lean_dec(v_a_980_);
lean_dec(v_declName_974_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___boxed(lean_object* v_declName_1031_, lean_object* v_upperBound_1032_, lean_object* v_majorPos_1033_, lean_object* v_numIndices_1034_, lean_object* v_xs_1035_, lean_object* v_Iargs_1036_, lean_object* v_a_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1031_, v_upperBound_1032_, v_majorPos_1033_, v_numIndices_1034_, v_xs_1035_, v_Iargs_1036_, v_a_1037_, v_b_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_Iargs_1036_);
lean_dec_ref(v_xs_1035_);
lean_dec(v_numIndices_1034_);
lean_dec(v_majorPos_1033_);
lean_dec(v_upperBound_1032_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(lean_object* v_declName_1047_, lean_object* v_xs_1048_, lean_object* v_majorPos_1049_, lean_object* v_numIndices_1050_, lean_object* v_Iargs_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v_indicesPos_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v_indicesPos_1058_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0));
v___x_1059_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1047_, v_numIndices_1050_, v_majorPos_1049_, v_numIndices_1050_, v_xs_1048_, v_Iargs_1051_, v___x_1057_, v_indicesPos_1058_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1068_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_array_to_list(v_a_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1059_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1059_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(lean_object* v_declName_1077_, lean_object* v_xs_1078_, lean_object* v_majorPos_1079_, lean_object* v_numIndices_1080_, lean_object* v_Iargs_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1077_, v_xs_1078_, v_majorPos_1079_, v_numIndices_1080_, v_Iargs_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec_ref(v_Iargs_1081_);
lean_dec(v_numIndices_1080_);
lean_dec(v_majorPos_1079_);
lean_dec_ref(v_xs_1078_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(lean_object* v_declName_1088_, lean_object* v_upperBound_1089_, lean_object* v_majorPos_1090_, lean_object* v_numIndices_1091_, lean_object* v_xs_1092_, lean_object* v_Iargs_1093_, lean_object* v_inst_1094_, lean_object* v_R_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_, lean_object* v_c_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1088_, v_upperBound_1089_, v_majorPos_1090_, v_numIndices_1091_, v_xs_1092_, v_Iargs_1093_, v_a_1096_, v_b_1097_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___boxed(lean_object* v_declName_1105_, lean_object* v_upperBound_1106_, lean_object* v_majorPos_1107_, lean_object* v_numIndices_1108_, lean_object* v_xs_1109_, lean_object* v_Iargs_1110_, lean_object* v_inst_1111_, lean_object* v_R_1112_, lean_object* v_a_1113_, lean_object* v_b_1114_, lean_object* v_c_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(v_declName_1105_, v_upperBound_1106_, v_majorPos_1107_, v_numIndices_1108_, v_xs_1109_, v_Iargs_1110_, v_inst_1111_, v_R_1112_, v_a_1113_, v_b_1114_, v_c_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec_ref(v_Iargs_1110_);
lean_dec_ref(v_xs_1109_);
lean_dec(v_numIndices_1108_);
lean_dec(v_majorPos_1107_);
lean_dec(v_upperBound_1106_);
return v_res_1121_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(lean_object* v_declName_1125_, lean_object* v_motiveResultType_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; 
if (lean_obj_tag(v_motiveResultType_1126_) == 3)
{
lean_object* v_u_1144_; 
v_u_1144_ = lean_ctor_get(v_motiveResultType_1126_, 0);
switch(lean_obj_tag(v_u_1144_))
{
case 0:
{
lean_object* v___x_1145_; 
lean_dec(v_declName_1125_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_u_1144_);
return v___x_1145_;
}
case 4:
{
lean_object* v___x_1146_; 
lean_dec(v_declName_1125_);
lean_inc_ref(v_u_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_u_1144_);
return v___x_1146_;
}
default: 
{
v___y_1133_ = v_a_1127_;
v___y_1134_ = v_a_1128_;
v___y_1135_ = v_a_1129_;
v___y_1136_ = v_a_1130_;
goto v___jp_1132_;
}
}
}
else
{
v___y_1133_ = v_a_1127_;
v___y_1134_ = v_a_1128_;
v___y_1135_ = v_a_1129_;
v___y_1136_ = v_a_1130_;
goto v___jp_1132_;
}
v___jp_1132_:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1137_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1138_ = 0;
v___x_1139_ = l_Lean_MessageData_ofConstName(v_declName_1125_, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1137_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1142_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(lean_object* v_declName_1147_, lean_object* v_motiveResultType_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1147_, v_motiveResultType_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_motiveResultType_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(lean_object* v___x_1155_, lean_object* v_as_1156_, lean_object* v_j_1157_){
_start:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_array_get_size(v_as_1156_);
v___x_1159_ = lean_nat_dec_lt(v_j_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_j_1157_);
v___x_1160_ = lean_box(0);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_array_fget_borrowed(v_as_1156_, v_j_1157_);
v___x_1162_ = lean_level_eq(v___x_1161_, v___x_1155_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_j_1157_, v___x_1163_);
lean_dec(v_j_1157_);
v_j_1157_ = v___x_1164_;
goto _start;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_j_1157_);
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0___boxed(lean_object* v___x_1167_, lean_object* v_as_1168_, lean_object* v_j_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_1167_, v_as_1168_, v_j_1169_);
lean_dec_ref(v_as_1168_);
lean_dec(v___x_1167_);
return v_res_1170_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(lean_object* v_motiveLvl_1174_, lean_object* v_Ilevels_1175_, lean_object* v_declName_1176_, lean_object* v_as_x27_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
if (lean_obj_tag(v_as_x27_1177_) == 0)
{
lean_object* v___x_1184_; 
lean_dec(v_declName_1176_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_b_1178_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_head_1185_ = lean_ctor_get(v_as_x27_1177_, 0);
v_tail_1186_ = lean_ctor_get(v_as_x27_1177_, 1);
lean_inc(v_head_1185_);
v___x_1187_ = l_Lean_mkLevelParam(v_head_1185_);
v___x_1188_ = lean_level_eq(v_motiveLvl_1174_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_1187_, v_Ilevels_1175_, v___x_1189_);
lean_dec(v___x_1187_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_b_1178_);
v___x_1191_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1192_ = l_Lean_MessageData_ofConstName(v_declName_1176_, v___x_1188_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
lean_inc(v_head_1185_);
v___x_1196_ = l_Lean_MessageData_ofName(v_head_1185_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1199_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1218_; 
v_val_1209_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1211_ = v___x_1190_;
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_val_1209_);
lean_dec(v___x_1190_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_val_1209_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_array_push(v_b_1178_, v___x_1214_);
v_as_x27_1177_ = v_tail_1186_;
v_b_1178_ = v___x_1215_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec(v___x_1187_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_array_push(v_b_1178_, v___x_1219_);
v_as_x27_1177_ = v_tail_1186_;
v_b_1178_ = v___x_1220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___boxed(lean_object* v_motiveLvl_1222_, lean_object* v_Ilevels_1223_, lean_object* v_declName_1224_, lean_object* v_as_x27_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1222_, v_Ilevels_1223_, v_declName_1224_, v_as_x27_1225_, v_b_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v_as_x27_1225_);
lean_dec_ref(v_Ilevels_1223_);
lean_dec(v_motiveLvl_1222_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(lean_object* v_declName_1235_, lean_object* v_lparams_1236_, lean_object* v_motiveLvl_1237_, lean_object* v_Ilevels_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_Ilevels_1244_; lean_object* v_univLevelPos_1245_; lean_object* v___x_1246_; 
v_Ilevels_1244_ = lean_array_mk(v_Ilevels_1238_);
v_univLevelPos_1245_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0));
v___x_1246_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1237_, v_Ilevels_1244_, v_declName_1235_, v_lparams_1236_, v_univLevelPos_1245_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec_ref(v_Ilevels_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1255_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_array_to_list(v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1246_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1246_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(lean_object* v_declName_1264_, lean_object* v_lparams_1265_, lean_object* v_motiveLvl_1266_, lean_object* v_Ilevels_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1264_, v_lparams_1265_, v_motiveLvl_1266_, v_Ilevels_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_motiveLvl_1266_);
lean_dec(v_lparams_1265_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(lean_object* v_motiveLvl_1274_, lean_object* v_Ilevels_1275_, lean_object* v_declName_1276_, lean_object* v_as_1277_, lean_object* v_as_x27_1278_, lean_object* v_b_1279_, lean_object* v_a_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1274_, v_Ilevels_1275_, v_declName_1276_, v_as_x27_1278_, v_b_1279_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___boxed(lean_object* v_motiveLvl_1287_, lean_object* v_Ilevels_1288_, lean_object* v_declName_1289_, lean_object* v_as_1290_, lean_object* v_as_x27_1291_, lean_object* v_b_1292_, lean_object* v_a_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(v_motiveLvl_1287_, v_Ilevels_1288_, v_declName_1289_, v_as_1290_, v_as_x27_1291_, v_b_1292_, v_a_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v_as_x27_1291_);
lean_dec(v_as_1290_);
lean_dec_ref(v_Ilevels_1288_);
lean_dec(v_motiveLvl_1287_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(lean_object* v_k_1300_, lean_object* v_b_1301_, lean_object* v_c_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
v___x_1308_ = lean_apply_7(v_k_1300_, v_b_1301_, v_c_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed(lean_object* v_k_1309_, lean_object* v_b_1310_, lean_object* v_c_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(v_k_1309_, v_b_1310_, v_c_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(lean_object* v_type_1318_, lean_object* v_k_1319_, uint8_t v_cleanupAnnotations_1320_, uint8_t v_whnfType_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1327_, 0, v_k_1319_);
v___x_1328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1318_, v___f_1327_, v_cleanupAnnotations_1320_, v_whnfType_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___boxed(lean_object* v_type_1345_, lean_object* v_k_1346_, lean_object* v_cleanupAnnotations_1347_, lean_object* v_whnfType_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1354_; uint8_t v_whnfType_boxed_1355_; lean_object* v_res_1356_; 
v_cleanupAnnotations_boxed_1354_ = lean_unbox(v_cleanupAnnotations_1347_);
v_whnfType_boxed_1355_ = lean_unbox(v_whnfType_1348_);
v_res_1356_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1345_, v_k_1346_, v_cleanupAnnotations_boxed_1354_, v_whnfType_boxed_1355_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(lean_object* v_00_u03b1_1357_, lean_object* v_type_1358_, lean_object* v_k_1359_, uint8_t v_cleanupAnnotations_1360_, uint8_t v_whnfType_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1358_, v_k_1359_, v_cleanupAnnotations_1360_, v_whnfType_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_type_1369_, lean_object* v_k_1370_, lean_object* v_cleanupAnnotations_1371_, lean_object* v_whnfType_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1378_; uint8_t v_whnfType_boxed_1379_; lean_object* v_res_1380_; 
v_cleanupAnnotations_boxed_1378_ = lean_unbox(v_cleanupAnnotations_1371_);
v_whnfType_boxed_1379_ = lean_unbox(v_whnfType_1372_);
v_res_1380_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(v_00_u03b1_1368_, v_type_1369_, v_k_1370_, v_cleanupAnnotations_boxed_1378_, v_whnfType_boxed_1379_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1380_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(lean_object* v_motive_1381_, lean_object* v_e_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_expr_eqv(v_e_1382_, v_motive_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed(lean_object* v_motive_1384_, lean_object* v_e_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(v_motive_1384_, v_e_1385_);
lean_dec_ref(v_e_1385_);
lean_dec_ref(v_motive_1384_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(lean_object* v_motive_1388_, uint8_t v___x_1389_, lean_object* v_as_1390_, size_t v_i_1391_, size_t v_stop_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_usize_dec_eq(v_i_1391_, v_stop_1392_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_array_uget_borrowed(v_as_1390_, v_i_1391_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___x_1399_);
v___x_1400_ = lean_infer_type(v___x_1399_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1419_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1419_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1419_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___f_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; 
lean_inc_ref(v_motive_1388_);
v___f_1405_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1405_, 0, v_motive_1388_);
v___x_1406_ = 1;
v___x_1407_ = lean_find_expr(v___f_1405_, v_a_1401_);
lean_dec(v_a_1401_);
lean_dec_ref(v___f_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
if (v___x_1389_ == 0)
{
size_t v___x_1408_; size_t v___x_1409_; 
lean_del_object(v___x_1403_);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1391_, v___x_1408_);
v_i_1391_ = v___x_1409_;
goto _start;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec_ref(v_motive_1388_);
v___x_1411_ = lean_box(v___x_1406_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1411_);
v___x_1413_ = v___x_1403_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_dec_ref(v___x_1407_);
lean_dec_ref(v_motive_1388_);
v___x_1415_ = lean_box(v___x_1406_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1415_);
v___x_1417_ = v___x_1403_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_motive_1388_);
v_a_1420_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1400_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1400_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_motive_1388_);
v___x_1428_ = 0;
v___x_1429_ = lean_box(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___boxed(lean_object* v_motive_1431_, lean_object* v___x_1432_, lean_object* v_as_1433_, lean_object* v_i_1434_, lean_object* v_stop_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v___x_4143__boxed_1441_; size_t v_i_boxed_1442_; size_t v_stop_boxed_1443_; lean_object* v_res_1444_; 
v___x_4143__boxed_1441_ = lean_unbox(v___x_1432_);
v_i_boxed_1442_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_stop_boxed_1443_ = lean_unbox_usize(v_stop_1435_);
lean_dec(v_stop_1435_);
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1431_, v___x_4143__boxed_1441_, v_as_1433_, v_i_boxed_1442_, v_stop_boxed_1443_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_as_1433_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(lean_object* v_motive_1445_, lean_object* v___x_1446_, uint8_t v___x_1447_, lean_object* v_minorArgs_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
if (lean_obj_tag(v_x_1449_) == 5)
{
lean_object* v_fn_1457_; lean_object* v_arg_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_fn_1457_ = lean_ctor_get(v_x_1449_, 0);
lean_inc_ref(v_fn_1457_);
v_arg_1458_ = lean_ctor_get(v_x_1449_, 1);
lean_inc_ref(v_arg_1458_);
lean_dec_ref(v_x_1449_);
v___x_1459_ = lean_array_set(v_x_1450_, v_x_1451_, v_arg_1458_);
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_sub(v_x_1451_, v___x_1460_);
lean_dec(v_x_1451_);
v_x_1449_ = v_fn_1457_;
v_x_1450_ = v___x_1459_;
v_x_1451_ = v___x_1461_;
goto _start;
}
else
{
uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v_recursor_1467_; 
lean_dec(v_x_1451_);
lean_dec_ref(v_x_1450_);
v___x_1463_ = lean_expr_eqv(v_x_1449_, v_motive_1445_);
lean_dec_ref(v_x_1449_);
v___x_1464_ = lean_box(v___x_1463_);
v___x_1465_ = lean_array_push(v___x_1446_, v___x_1464_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_array_get_size(v_minorArgs_1448_);
v___x_1473_ = lean_nat_dec_lt(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v_motive_1445_);
v_recursor_1467_ = v___x_1447_;
goto v___jp_1466_;
}
else
{
if (v___x_1473_ == 0)
{
lean_dec_ref(v_motive_1445_);
v_recursor_1467_ = v___x_1447_;
goto v___jp_1466_;
}
else
{
size_t v___x_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = lean_usize_of_nat(v___x_1472_);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1445_, v___x_1447_, v_minorArgs_1448_, v___x_1474_, v___x_1475_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; uint8_t v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = lean_unbox(v_a_1477_);
lean_dec(v_a_1477_);
v_recursor_1467_ = v___x_1478_;
goto v___jp_1466_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v___x_1465_);
v_a_1479_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1476_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1476_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_motive_1445_);
v_recursor_1467_ = v___x_1447_;
goto v___jp_1466_;
}
v___jp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = lean_box(v_recursor_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1465_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1___boxed(lean_object* v_motive_1487_, lean_object* v___x_1488_, lean_object* v___x_1489_, lean_object* v_minorArgs_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v___x_4229__boxed_1499_; lean_object* v_res_1500_; 
v___x_4229__boxed_1499_ = lean_unbox(v___x_1489_);
v_res_1500_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1487_, v___x_1488_, v___x_4229__boxed_1499_, v_minorArgs_1490_, v_x_1491_, v_x_1492_, v_x_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec_ref(v_minorArgs_1490_);
return v_res_1500_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1501_; lean_object* v_dummy_1502_; 
v___x_1501_ = lean_box(0);
v_dummy_1502_ = l_Lean_Expr_sort___override(v___x_1501_);
return v_dummy_1502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(lean_object* v_motive_1503_, lean_object* v_fst_1504_, lean_object* v_snd_1505_, lean_object* v_minorArgs_1506_, lean_object* v_minorResultType_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_dummy_1513_; lean_object* v_nargs_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; 
v_dummy_1513_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_1514_ = l_Lean_Expr_getAppNumArgs(v_minorResultType_1507_);
lean_inc(v_nargs_1514_);
v___x_1515_ = lean_mk_array(v_nargs_1514_, v_dummy_1513_);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_sub(v_nargs_1514_, v___x_1516_);
lean_dec(v_nargs_1514_);
v___x_1518_ = lean_unbox(v_snd_1505_);
v___x_1519_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1503_, v_fst_1504_, v___x_1518_, v_minorArgs_1506_, v_minorResultType_1507_, v___x_1515_, v___x_1517_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed(lean_object* v_motive_1520_, lean_object* v_fst_1521_, lean_object* v_snd_1522_, lean_object* v_minorArgs_1523_, lean_object* v_minorResultType_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(v_motive_1520_, v_fst_1521_, v_snd_1522_, v_minorArgs_1523_, v_minorResultType_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_minorArgs_1523_);
lean_dec(v_snd_1522_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(lean_object* v_upperBound_1531_, lean_object* v_motive_1532_, lean_object* v_xs_1533_, lean_object* v_numParams_1534_, lean_object* v_majorPos_1535_, lean_object* v_numIndices_1536_, lean_object* v_a_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_a_1545_; uint8_t v___x_1549_; 
v___x_1549_ = lean_nat_dec_lt(v_a_1537_, v_upperBound_1531_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_dec(v_a_1537_);
lean_dec_ref(v_motive_1532_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_b_1538_);
return v___x_1550_;
}
else
{
lean_object* v_fst_1551_; lean_object* v_snd_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1583_; 
v_fst_1551_ = lean_ctor_get(v_b_1538_, 0);
v_snd_1552_ = lean_ctor_get(v_b_1538_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_b_1538_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1554_ = v_b_1538_;
v_isShared_1555_ = v_isSharedCheck_1583_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_snd_1552_);
lean_inc(v_fst_1551_);
lean_dec(v_b_1538_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1583_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v_recursor_1558_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_numParams_1534_, v___x_1556_);
v_recursor_1558_ = lean_nat_dec_lt(v_a_1537_, v___x_1557_);
lean_dec(v___x_1557_);
if (v_recursor_1558_ == 0)
{
lean_object* v___f_1559_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
lean_inc(v_snd_1552_);
lean_inc(v_fst_1551_);
lean_inc_ref(v_motive_1532_);
v___f_1559_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1559_, 0, v_motive_1532_);
lean_closure_set(v___f_1559_, 1, v_fst_1551_);
lean_closure_set(v___f_1559_, 2, v_snd_1552_);
v___x_1574_ = lean_nat_sub(v_majorPos_1535_, v_numIndices_1536_);
v___x_1575_ = lean_nat_dec_le(v___x_1574_, v_a_1537_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_del_object(v___x_1554_);
lean_dec(v_snd_1552_);
lean_dec(v_fst_1551_);
goto v___jp_1560_;
}
else
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_nat_dec_le(v_a_1537_, v_majorPos_1535_);
if (v___x_1576_ == 0)
{
lean_del_object(v___x_1554_);
lean_dec(v_snd_1552_);
lean_dec(v_fst_1551_);
goto v___jp_1560_;
}
else
{
lean_object* v___x_1578_; 
lean_dec_ref(v___f_1559_);
if (v_isShared_1555_ == 0)
{
v___x_1578_ = v___x_1554_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_fst_1551_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_snd_1552_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v_a_1545_ = v___x_1578_;
goto v___jp_1544_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_array_fget_borrowed(v_xs_1533_, v_a_1537_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___x_1561_);
v___x_1562_ = lean_infer_type(v___x_1561_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_1563_, v___f_1559_, v_recursor_1558_, v_recursor_1558_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
v_a_1545_ = v_a_1565_;
goto v___jp_1544_;
}
else
{
lean_dec(v_a_1537_);
lean_dec_ref(v_motive_1532_);
return v___x_1564_;
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v___f_1559_);
lean_dec(v_a_1537_);
lean_dec_ref(v_motive_1532_);
v_a_1566_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1562_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1562_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_object* v___x_1581_; 
if (v_isShared_1555_ == 0)
{
v___x_1581_ = v___x_1554_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_fst_1551_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_snd_1552_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v_a_1545_ = v___x_1581_;
goto v___jp_1544_;
}
}
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v_a_1537_, v___x_1546_);
lean_dec(v_a_1537_);
v_a_1537_ = v___x_1547_;
v_b_1538_ = v_a_1545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___boxed(lean_object* v_upperBound_1584_, lean_object* v_motive_1585_, lean_object* v_xs_1586_, lean_object* v_numParams_1587_, lean_object* v_majorPos_1588_, lean_object* v_numIndices_1589_, lean_object* v_a_1590_, lean_object* v_b_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1584_, v_motive_1585_, v_xs_1586_, v_numParams_1587_, v_majorPos_1588_, v_numIndices_1589_, v_a_1590_, v_b_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v_numIndices_1589_);
lean_dec(v_majorPos_1588_);
lean_dec(v_numParams_1587_);
lean_dec_ref(v_xs_1586_);
lean_dec(v_upperBound_1584_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(lean_object* v_xs_1604_, lean_object* v_numParams_1605_, lean_object* v_numIndices_1606_, lean_object* v_majorPos_1607_, lean_object* v_motive_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1614_ = lean_array_get_size(v_xs_1604_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1));
v___x_1617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v___x_1614_, v_motive_1608_, v_xs_1604_, v_numParams_1605_, v_majorPos_1607_, v_numIndices_1606_, v___x_1615_, v___x_1616_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1635_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1635_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1635_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1634_; 
v_fst_1622_ = lean_ctor_get(v_a_1618_, 0);
v_snd_1623_ = lean_ctor_get(v_a_1618_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1625_ = v_a_1618_;
v_isShared_1626_ = v_isSharedCheck_1634_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v_a_1618_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1634_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_array_to_list(v_fst_1622_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_snd_1623_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1629_);
v___x_1631_ = v___x_1620_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1617_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1617_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(lean_object* v_xs_1644_, lean_object* v_numParams_1645_, lean_object* v_numIndices_1646_, lean_object* v_majorPos_1647_, lean_object* v_motive_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1644_, v_numParams_1645_, v_numIndices_1646_, v_majorPos_1647_, v_motive_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_majorPos_1647_);
lean_dec(v_numIndices_1646_);
lean_dec(v_numParams_1645_);
lean_dec_ref(v_xs_1644_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(lean_object* v_upperBound_1655_, lean_object* v_motive_1656_, lean_object* v_xs_1657_, lean_object* v_numParams_1658_, lean_object* v_majorPos_1659_, lean_object* v_numIndices_1660_, lean_object* v_inst_1661_, lean_object* v_R_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v_c_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1655_, v_motive_1656_, v_xs_1657_, v_numParams_1658_, v_majorPos_1659_, v_numIndices_1660_, v_a_1663_, v_b_1664_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___boxed(lean_object* v_upperBound_1672_, lean_object* v_motive_1673_, lean_object* v_xs_1674_, lean_object* v_numParams_1675_, lean_object* v_majorPos_1676_, lean_object* v_numIndices_1677_, lean_object* v_inst_1678_, lean_object* v_R_1679_, lean_object* v_a_1680_, lean_object* v_b_1681_, lean_object* v_c_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(v_upperBound_1672_, v_motive_1673_, v_xs_1674_, v_numParams_1675_, v_majorPos_1676_, v_numIndices_1677_, v_inst_1678_, v_R_1679_, v_a_1680_, v_b_1681_, v_c_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_numIndices_1677_);
lean_dec(v_majorPos_1676_);
lean_dec(v_numParams_1675_);
lean_dec_ref(v_xs_1674_);
lean_dec(v_upperBound_1672_);
return v_res_1688_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(lean_object* v_declName_1692_, lean_object* v_motiveArgs_1693_, lean_object* v_motiveResultType_1694_, lean_object* v_motiveTypeParams_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = l_Lean_Expr_isSort(v_motiveResultType_1694_);
if (v___x_1709_ == 0)
{
goto v___jp_1701_;
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = lean_array_get_size(v_motiveArgs_1693_);
v___x_1711_ = lean_array_get_size(v_motiveTypeParams_1695_);
v___x_1712_ = lean_nat_dec_eq(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
goto v___jp_1701_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_declName_1692_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
v___jp_1701_:
{
lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1703_ = 0;
v___x_1704_ = l_Lean_MessageData_ofConstName(v_declName_1692_, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1702_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1707_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(lean_object* v_declName_1715_, lean_object* v_motiveArgs_1716_, lean_object* v_motiveResultType_1717_, lean_object* v_motiveTypeParams_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1715_, v_motiveArgs_1716_, v_motiveResultType_1717_, v_motiveTypeParams_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec_ref(v_motiveTypeParams_1718_);
lean_dec_ref(v_motiveResultType_1717_);
lean_dec_ref(v_motiveArgs_1716_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(lean_object* v_declName_1725_, lean_object* v_motiveArgs_1726_, lean_object* v_a_1727_, lean_object* v_us_1728_, lean_object* v_xs_1729_, lean_object* v___x_1730_, lean_object* v___y_1731_, lean_object* v_fst_1732_, lean_object* v_motive_1733_, lean_object* v_declName_1734_, uint8_t v_snd_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_motiveTypeParams_1738_, lean_object* v_motiveResultType_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
lean_inc(v_declName_1725_);
v___x_1745_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1725_, v_motiveArgs_1726_, v_motiveResultType_1739_, v_motiveTypeParams_1738_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; 
lean_dec_ref(v___x_1745_);
lean_inc(v_declName_1725_);
v___x_1746_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1725_, v_motiveResultType_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = l_Lean_ConstantInfo_levelParams(v_a_1727_);
lean_inc(v_declName_1725_);
v___x_1749_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1725_, v___x_1748_, v_a_1747_, v_us_1728_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v_a_1747_);
lean_dec(v___x_1748_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1729_, v___x_1730_, v___y_1731_, v_fst_1732_, v_motive_1733_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1764_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1764_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1764_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_fst_1756_; lean_object* v_snd_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1762_; 
v_fst_1756_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_fst_1756_);
v_snd_1757_ = lean_ctor_get(v_a_1752_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_a_1752_);
v___x_1758_ = lean_array_get_size(v_xs_1729_);
v___x_1759_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1759_, 0, v_declName_1725_);
lean_ctor_set(v___x_1759_, 1, v_declName_1734_);
lean_ctor_set(v___x_1759_, 2, v_a_1750_);
lean_ctor_set(v___x_1759_, 3, v___x_1758_);
lean_ctor_set(v___x_1759_, 4, v_fst_1732_);
lean_ctor_set(v___x_1759_, 5, v_a_1736_);
lean_ctor_set(v___x_1759_, 6, v_a_1737_);
lean_ctor_set(v___x_1759_, 7, v_fst_1756_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*8, v_snd_1735_);
v___x_1760_ = lean_unbox(v_snd_1757_);
lean_dec(v_snd_1757_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*8 + 1, v___x_1760_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1759_);
v___x_1762_ = v___x_1754_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1759_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_a_1750_);
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec(v_declName_1734_);
lean_dec(v_fst_1732_);
lean_dec(v_declName_1725_);
v_a_1765_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1751_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1751_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec(v_declName_1734_);
lean_dec_ref(v_motive_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_declName_1725_);
v_a_1773_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1749_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1749_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec(v_declName_1734_);
lean_dec_ref(v_motive_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_us_1728_);
lean_dec(v_declName_1725_);
v_a_1781_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1746_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1746_);
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
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec(v_declName_1734_);
lean_dec_ref(v_motive_1733_);
lean_dec(v_fst_1732_);
lean_dec(v_us_1728_);
lean_dec(v_declName_1725_);
v_a_1789_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1745_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1745_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v_declName_1797_ = _args[0];
lean_object* v_motiveArgs_1798_ = _args[1];
lean_object* v_a_1799_ = _args[2];
lean_object* v_us_1800_ = _args[3];
lean_object* v_xs_1801_ = _args[4];
lean_object* v___x_1802_ = _args[5];
lean_object* v___y_1803_ = _args[6];
lean_object* v_fst_1804_ = _args[7];
lean_object* v_motive_1805_ = _args[8];
lean_object* v_declName_1806_ = _args[9];
lean_object* v_snd_1807_ = _args[10];
lean_object* v_a_1808_ = _args[11];
lean_object* v_a_1809_ = _args[12];
lean_object* v_motiveTypeParams_1810_ = _args[13];
lean_object* v_motiveResultType_1811_ = _args[14];
lean_object* v___y_1812_ = _args[15];
lean_object* v___y_1813_ = _args[16];
lean_object* v___y_1814_ = _args[17];
lean_object* v___y_1815_ = _args[18];
lean_object* v___y_1816_ = _args[19];
_start:
{
uint8_t v_snd_5191__boxed_1817_; lean_object* v_res_1818_; 
v_snd_5191__boxed_1817_ = lean_unbox(v_snd_1807_);
v_res_1818_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(v_declName_1797_, v_motiveArgs_1798_, v_a_1799_, v_us_1800_, v_xs_1801_, v___x_1802_, v___y_1803_, v_fst_1804_, v_motive_1805_, v_declName_1806_, v_snd_5191__boxed_1817_, v_a_1808_, v_a_1809_, v_motiveTypeParams_1810_, v_motiveResultType_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_motiveResultType_1811_);
lean_dec_ref(v_motiveTypeParams_1810_);
lean_dec(v___y_1803_);
lean_dec(v___x_1802_);
lean_dec_ref(v_xs_1801_);
lean_dec_ref(v_a_1799_);
lean_dec_ref(v_motiveArgs_1798_);
return v_res_1818_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(lean_object* v_declName_1822_, lean_object* v_xs_1823_, lean_object* v___x_1824_, lean_object* v_fst_1825_, lean_object* v___y_1826_, lean_object* v_motiveArgs_1827_, lean_object* v_a_1828_, lean_object* v_motive_1829_, uint8_t v_snd_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
if (lean_obj_tag(v_x_1831_) == 5)
{
lean_object* v_fn_1839_; lean_object* v_arg_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_fn_1839_ = lean_ctor_get(v_x_1831_, 0);
lean_inc_ref(v_fn_1839_);
v_arg_1840_ = lean_ctor_get(v_x_1831_, 1);
lean_inc_ref(v_arg_1840_);
lean_dec_ref(v_x_1831_);
v___x_1841_ = lean_array_set(v_x_1832_, v_x_1833_, v_arg_1840_);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_nat_sub(v_x_1833_, v___x_1842_);
lean_dec(v_x_1833_);
v_x_1831_ = v_fn_1839_;
v_x_1832_ = v___x_1841_;
v_x_1833_ = v___x_1843_;
goto _start;
}
else
{
lean_dec(v_x_1833_);
if (lean_obj_tag(v_x_1831_) == 4)
{
lean_object* v_declName_1845_; lean_object* v_us_1846_; lean_object* v___x_1847_; 
v_declName_1845_ = lean_ctor_get(v_x_1831_, 0);
lean_inc(v_declName_1845_);
v_us_1846_ = lean_ctor_get(v_x_1831_, 1);
lean_inc(v_us_1846_);
lean_dec_ref(v_x_1831_);
lean_inc(v_declName_1822_);
v___x_1847_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_1822_, v_xs_1823_, v___x_1824_, v_x_1832_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
lean_inc(v_declName_1822_);
v___x_1849_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1822_, v_xs_1823_, v_fst_1825_, v___y_1826_, v_x_1832_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec_ref(v_x_1832_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc_ref(v_motive_1829_);
v___x_1851_ = lean_infer_type(v_motive_1829_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; lean_object* v___f_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = lean_box(v_snd_1830_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed), 20, 13);
lean_closure_set(v___f_1854_, 0, v_declName_1822_);
lean_closure_set(v___f_1854_, 1, v_motiveArgs_1827_);
lean_closure_set(v___f_1854_, 2, v_a_1828_);
lean_closure_set(v___f_1854_, 3, v_us_1846_);
lean_closure_set(v___f_1854_, 4, v_xs_1823_);
lean_closure_set(v___f_1854_, 5, v___x_1824_);
lean_closure_set(v___f_1854_, 6, v___y_1826_);
lean_closure_set(v___f_1854_, 7, v_fst_1825_);
lean_closure_set(v___f_1854_, 8, v_motive_1829_);
lean_closure_set(v___f_1854_, 9, v_declName_1845_);
lean_closure_set(v___f_1854_, 10, v___x_1853_);
lean_closure_set(v___f_1854_, 11, v_a_1848_);
lean_closure_set(v___f_1854_, 12, v_a_1850_);
v___x_1855_ = 0;
v___x_1856_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_1852_, v___f_1854_, v___x_1855_, v___x_1855_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1856_;
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1850_);
lean_dec(v_a_1848_);
lean_dec(v_us_1846_);
lean_dec(v_declName_1845_);
lean_dec_ref(v_motive_1829_);
lean_dec_ref(v_a_1828_);
lean_dec_ref(v_motiveArgs_1827_);
lean_dec(v___y_1826_);
lean_dec(v_fst_1825_);
lean_dec(v___x_1824_);
lean_dec_ref(v_xs_1823_);
lean_dec(v_declName_1822_);
v_a_1857_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1851_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1851_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_a_1848_);
lean_dec(v_us_1846_);
lean_dec(v_declName_1845_);
lean_dec_ref(v_motive_1829_);
lean_dec_ref(v_a_1828_);
lean_dec_ref(v_motiveArgs_1827_);
lean_dec(v___y_1826_);
lean_dec(v_fst_1825_);
lean_dec(v___x_1824_);
lean_dec_ref(v_xs_1823_);
lean_dec(v_declName_1822_);
v_a_1865_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1849_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1849_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_us_1846_);
lean_dec(v_declName_1845_);
lean_dec_ref(v_x_1832_);
lean_dec_ref(v_motive_1829_);
lean_dec_ref(v_a_1828_);
lean_dec_ref(v_motiveArgs_1827_);
lean_dec(v___y_1826_);
lean_dec(v_fst_1825_);
lean_dec(v___x_1824_);
lean_dec_ref(v_xs_1823_);
lean_dec(v_declName_1822_);
v_a_1873_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1847_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1847_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec_ref(v_x_1832_);
lean_dec_ref(v_x_1831_);
lean_dec_ref(v_motive_1829_);
lean_dec_ref(v_a_1828_);
lean_dec_ref(v_motiveArgs_1827_);
lean_dec(v___y_1826_);
lean_dec(v_fst_1825_);
lean_dec(v___x_1824_);
lean_dec_ref(v_xs_1823_);
v___x_1881_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1882_ = 0;
v___x_1883_ = l_Lean_MessageData_ofConstName(v_declName_1822_, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1886_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___boxed(lean_object** _args){
lean_object* v_declName_1888_ = _args[0];
lean_object* v_xs_1889_ = _args[1];
lean_object* v___x_1890_ = _args[2];
lean_object* v_fst_1891_ = _args[3];
lean_object* v___y_1892_ = _args[4];
lean_object* v_motiveArgs_1893_ = _args[5];
lean_object* v_a_1894_ = _args[6];
lean_object* v_motive_1895_ = _args[7];
lean_object* v_snd_1896_ = _args[8];
lean_object* v_x_1897_ = _args[9];
lean_object* v_x_1898_ = _args[10];
lean_object* v_x_1899_ = _args[11];
lean_object* v___y_1900_ = _args[12];
lean_object* v___y_1901_ = _args[13];
lean_object* v___y_1902_ = _args[14];
lean_object* v___y_1903_ = _args[15];
lean_object* v___y_1904_ = _args[16];
_start:
{
uint8_t v_snd_5345__boxed_1905_; lean_object* v_res_1906_; 
v_snd_5345__boxed_1905_ = lean_unbox(v_snd_1896_);
v_res_1906_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1888_, v_xs_1889_, v___x_1890_, v_fst_1891_, v___y_1892_, v_motiveArgs_1893_, v_a_1894_, v_motive_1895_, v_snd_5345__boxed_1905_, v_x_1897_, v_x_1898_, v_x_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1906_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(lean_object* v_declName_1910_, lean_object* v_a_1911_, lean_object* v_xs_1912_, lean_object* v_a_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 5)
{
lean_object* v_fn_1922_; lean_object* v_arg_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_fn_1922_ = lean_ctor_get(v_x_1914_, 0);
lean_inc_ref(v_fn_1922_);
v_arg_1923_ = lean_ctor_get(v_x_1914_, 1);
lean_inc_ref(v_arg_1923_);
lean_dec_ref(v_x_1914_);
v___x_1924_ = lean_array_set(v_x_1915_, v_x_1916_, v_arg_1923_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_sub(v_x_1916_, v___x_1925_);
lean_dec(v_x_1916_);
v_x_1914_ = v_fn_1922_;
v_x_1915_ = v___x_1924_;
v_x_1916_ = v___x_1926_;
goto _start;
}
else
{
lean_object* v___x_1928_; 
lean_dec(v_x_1916_);
lean_inc(v_declName_1910_);
v___x_1928_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_1910_, v_x_1914_, v_x_1915_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1929_; 
lean_dec_ref(v___x_1928_);
lean_inc(v_declName_1910_);
v___x_1929_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_1910_, v_a_1911_, v_xs_1912_, v_x_1915_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v_snd_1931_; lean_object* v_fst_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1994_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v_snd_1931_ = lean_ctor_get(v_a_1930_, 1);
v_fst_1932_ = lean_ctor_get(v_a_1930_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_a_1930_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1934_ = v_a_1930_;
v_isShared_1935_ = v_isSharedCheck_1994_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snd_1931_);
lean_inc(v_fst_1932_);
lean_dec(v_a_1930_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1994_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1993_; 
v_fst_1936_ = lean_ctor_get(v_snd_1931_, 0);
v_snd_1937_ = lean_ctor_get(v_snd_1931_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_snd_1931_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1939_ = v_snd_1931_;
v_isShared_1940_ = v_isSharedCheck_1993_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_snd_1937_);
lean_inc(v_fst_1936_);
lean_dec(v_snd_1931_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1993_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1967_; uint8_t v___x_1988_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(v_xs_1912_, v_x_1914_, v___x_1941_);
v___x_1988_ = lean_unbox(v_snd_1937_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_array_get_size(v_x_1915_);
v___y_1967_ = v___x_1989_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_array_get_size(v_x_1915_);
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = lean_nat_sub(v___x_1990_, v___x_1991_);
v___y_1967_ = v___x_1992_;
goto v___jp_1966_;
}
v___jp_1943_:
{
lean_object* v___x_1949_; 
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v___x_1949_ = lean_infer_type(v_fst_1932_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v_dummy_1951_; lean_object* v_nargs_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v_dummy_1951_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_1952_ = l_Lean_Expr_getAppNumArgs(v_a_1950_);
lean_inc(v_nargs_1952_);
v___x_1953_ = lean_mk_array(v_nargs_1952_, v_dummy_1951_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_sub(v_nargs_1952_, v___x_1954_);
lean_dec(v_nargs_1952_);
v___x_1956_ = lean_unbox(v_snd_1937_);
lean_dec(v_snd_1937_);
v___x_1957_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1910_, v_xs_1912_, v___x_1942_, v_fst_1936_, v___y_1944_, v_x_1915_, v_a_1913_, v_x_1914_, v___x_1956_, v_a_1950_, v___x_1953_, v___x_1955_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1957_;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v___y_1944_);
lean_dec(v___x_1942_);
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
lean_dec_ref(v_x_1915_);
lean_dec_ref(v_x_1914_);
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_xs_1912_);
lean_dec(v_declName_1910_);
v_a_1958_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1949_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1949_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
v___jp_1966_:
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_nat_dec_lt(v_fst_1936_, v___y_1967_);
if (v___x_1968_ == 0)
{
lean_del_object(v___x_1939_);
lean_del_object(v___x_1934_);
v___y_1944_ = v___y_1967_;
v___y_1945_ = v___y_1917_;
v___y_1946_ = v___y_1918_;
v___y_1947_ = v___y_1919_;
v___y_1948_ = v___y_1920_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
lean_dec(v___y_1967_);
lean_dec(v___x_1942_);
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
lean_dec(v_fst_1932_);
lean_dec_ref(v_x_1915_);
lean_dec_ref(v_x_1914_);
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_xs_1912_);
v___x_1969_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1970_ = 0;
v___x_1971_ = l_Lean_MessageData_ofConstName(v_declName_1910_, v___x_1970_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 7);
lean_ctor_set(v___x_1939_, 1, v___x_1971_);
lean_ctor_set(v___x_1939_, 0, v___x_1969_);
v___x_1973_ = v___x_1939_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 7);
lean_ctor_set(v___x_1934_, 1, v___x_1974_);
lean_ctor_set(v___x_1934_, 0, v___x_1973_);
v___x_1976_ = v___x_1934_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v___x_1977_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1976_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
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
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_x_1915_);
lean_dec_ref(v_x_1914_);
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_xs_1912_);
lean_dec(v_declName_1910_);
v_a_1995_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1929_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1929_);
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
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_x_1915_);
lean_dec_ref(v_x_1914_);
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_xs_1912_);
lean_dec(v_a_1911_);
lean_dec(v_declName_1910_);
v_a_2003_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1928_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1928_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___boxed(lean_object* v_declName_2011_, lean_object* v_a_2012_, lean_object* v_xs_2013_, lean_object* v_a_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_2011_, v_a_2012_, v_xs_2013_, v_a_2014_, v_x_2015_, v_x_2016_, v_x_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(lean_object* v_declName_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_xs_2027_, lean_object* v_type_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_dummy_2034_; lean_object* v_nargs_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_dummy_2034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_2035_ = l_Lean_Expr_getAppNumArgs(v_type_2028_);
lean_inc(v_nargs_2035_);
v___x_2036_ = lean_mk_array(v_nargs_2035_, v_dummy_2034_);
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_sub(v_nargs_2035_, v___x_2037_);
lean_dec(v_nargs_2035_);
v___x_2039_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_2024_, v_a_2025_, v_xs_2027_, v_a_2026_, v_type_2028_, v___x_2036_, v___x_2038_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed(lean_object* v_declName_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_xs_2043_, lean_object* v_type_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(v_declName_2040_, v_a_2041_, v_a_2042_, v_xs_2043_, v_type_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_2051_, lean_object* v_msg_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_fileName_2058_; lean_object* v_fileMap_2059_; lean_object* v_options_2060_; lean_object* v_currRecDepth_2061_; lean_object* v_maxRecDepth_2062_; lean_object* v_ref_2063_; lean_object* v_currNamespace_2064_; lean_object* v_openDecls_2065_; lean_object* v_initHeartbeats_2066_; lean_object* v_maxHeartbeats_2067_; lean_object* v_quotContext_2068_; lean_object* v_currMacroScope_2069_; uint8_t v_diag_2070_; lean_object* v_cancelTk_x3f_2071_; uint8_t v_suppressElabErrors_2072_; lean_object* v_inheritedTraceOptions_2073_; lean_object* v_ref_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_fileName_2058_ = lean_ctor_get(v___y_2055_, 0);
v_fileMap_2059_ = lean_ctor_get(v___y_2055_, 1);
v_options_2060_ = lean_ctor_get(v___y_2055_, 2);
v_currRecDepth_2061_ = lean_ctor_get(v___y_2055_, 3);
v_maxRecDepth_2062_ = lean_ctor_get(v___y_2055_, 4);
v_ref_2063_ = lean_ctor_get(v___y_2055_, 5);
v_currNamespace_2064_ = lean_ctor_get(v___y_2055_, 6);
v_openDecls_2065_ = lean_ctor_get(v___y_2055_, 7);
v_initHeartbeats_2066_ = lean_ctor_get(v___y_2055_, 8);
v_maxHeartbeats_2067_ = lean_ctor_get(v___y_2055_, 9);
v_quotContext_2068_ = lean_ctor_get(v___y_2055_, 10);
v_currMacroScope_2069_ = lean_ctor_get(v___y_2055_, 11);
v_diag_2070_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*14);
v_cancelTk_x3f_2071_ = lean_ctor_get(v___y_2055_, 12);
v_suppressElabErrors_2072_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2073_ = lean_ctor_get(v___y_2055_, 13);
v_ref_2074_ = l_Lean_replaceRef(v_ref_2051_, v_ref_2063_);
lean_inc_ref(v_inheritedTraceOptions_2073_);
lean_inc(v_cancelTk_x3f_2071_);
lean_inc(v_currMacroScope_2069_);
lean_inc(v_quotContext_2068_);
lean_inc(v_maxHeartbeats_2067_);
lean_inc(v_initHeartbeats_2066_);
lean_inc(v_openDecls_2065_);
lean_inc(v_currNamespace_2064_);
lean_inc(v_maxRecDepth_2062_);
lean_inc(v_currRecDepth_2061_);
lean_inc_ref(v_options_2060_);
lean_inc_ref(v_fileMap_2059_);
lean_inc_ref(v_fileName_2058_);
v___x_2075_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2075_, 0, v_fileName_2058_);
lean_ctor_set(v___x_2075_, 1, v_fileMap_2059_);
lean_ctor_set(v___x_2075_, 2, v_options_2060_);
lean_ctor_set(v___x_2075_, 3, v_currRecDepth_2061_);
lean_ctor_set(v___x_2075_, 4, v_maxRecDepth_2062_);
lean_ctor_set(v___x_2075_, 5, v_ref_2074_);
lean_ctor_set(v___x_2075_, 6, v_currNamespace_2064_);
lean_ctor_set(v___x_2075_, 7, v_openDecls_2065_);
lean_ctor_set(v___x_2075_, 8, v_initHeartbeats_2066_);
lean_ctor_set(v___x_2075_, 9, v_maxHeartbeats_2067_);
lean_ctor_set(v___x_2075_, 10, v_quotContext_2068_);
lean_ctor_set(v___x_2075_, 11, v_currMacroScope_2069_);
lean_ctor_set(v___x_2075_, 12, v_cancelTk_x3f_2071_);
lean_ctor_set(v___x_2075_, 13, v_inheritedTraceOptions_2073_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*14, v_diag_2070_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*14 + 1, v_suppressElabErrors_2072_);
v___x_2076_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_2052_, v___y_2053_, v___y_2054_, v___x_2075_, v___y_2056_);
lean_dec_ref(v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_2077_, lean_object* v_msg_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2077_, v_msg_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v_ref_2077_);
return v_res_2084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_ctor_set(v___x_2090_, 2, v___x_2089_);
lean_ctor_set(v___x_2090_, 3, v___x_2089_);
lean_ctor_set(v___x_2090_, 4, v___x_2088_);
lean_ctor_set(v___x_2090_, 5, v___x_2088_);
lean_ctor_set(v___x_2090_, 6, v___x_2088_);
lean_ctor_set(v___x_2090_, 7, v___x_2088_);
lean_ctor_set(v___x_2090_, 8, v___x_2088_);
lean_ctor_set(v___x_2090_, 9, v___x_2088_);
return v___x_2090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_unsigned_to_nat(32u);
v___x_2092_ = lean_mk_empty_array_with_capacity(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2094_ = ((size_t)5ULL);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_unsigned_to_nat(32u);
v___x_2097_ = lean_mk_empty_array_with_capacity(v___x_2096_);
v___x_2098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_2099_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2097_);
lean_ctor_set(v___x_2099_, 2, v___x_2095_);
lean_ctor_set(v___x_2099_, 3, v___x_2095_);
lean_ctor_set_usize(v___x_2099_, 4, v___x_2094_);
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2100_ = lean_box(1);
v___x_2101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2100_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_2125_, lean_object* v_declHint_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v_env_2130_; uint8_t v___x_2131_; 
v___x_2129_ = lean_st_ref_get(v___y_2127_);
v_env_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc_ref(v_env_2130_);
lean_dec(v___x_2129_);
v___x_2131_ = l_Lean_Name_isAnonymous(v_declHint_2126_);
if (v___x_2131_ == 0)
{
uint8_t v_isExporting_2132_; 
v_isExporting_2132_ = lean_ctor_get_uint8(v_env_2130_, sizeof(void*)*8);
if (v_isExporting_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_msg_2125_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
lean_inc_ref(v_env_2130_);
v___x_2134_ = l_Lean_Environment_setExporting(v_env_2130_, v___x_2131_);
lean_inc(v_declHint_2126_);
lean_inc_ref(v___x_2134_);
v___x_2135_ = l_Lean_Environment_contains(v___x_2134_, v_declHint_2126_, v_isExporting_2132_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec_ref(v___x_2134_);
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_msg_2125_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_c_2142_; lean_object* v___x_2143_; 
v___x_2137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_2139_ = l_Lean_Options_empty;
v___x_2140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2134_);
lean_ctor_set(v___x_2140_, 1, v___x_2137_);
lean_ctor_set(v___x_2140_, 2, v___x_2138_);
lean_ctor_set(v___x_2140_, 3, v___x_2139_);
lean_inc(v_declHint_2126_);
v___x_2141_ = l_Lean_MessageData_ofConstName(v_declHint_2126_, v___x_2131_);
v_c_2142_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2142_, 0, v___x_2140_);
lean_ctor_set(v_c_2142_, 1, v___x_2141_);
v___x_2143_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2130_, v_declHint_2126_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_c_2142_);
v___x_2146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_MessageData_note(v___x_2147_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_msg_2125_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
else
{
lean_object* v_val_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2186_; 
v_val_2151_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2153_ = v___x_2143_;
v_isShared_2154_ = v_isSharedCheck_2186_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_val_2151_);
lean_dec(v___x_2143_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2186_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_mod_2158_; uint8_t v___x_2159_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = l_Lean_Environment_header(v_env_2130_);
lean_dec_ref(v_env_2130_);
v___x_2157_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2156_);
v_mod_2158_ = lean_array_get(v___x_2155_, v___x_2157_, v_val_2151_);
lean_dec(v_val_2151_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = l_Lean_isPrivateName(v_declHint_2126_);
lean_dec(v_declHint_2126_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_c_2142_);
v___x_2162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Lean_MessageData_ofName(v_mod_2158_);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = l_Lean_MessageData_note(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v_msg_2125_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2169_);
v___x_2171_ = v___x_2153_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_c_2142_);
v___x_2175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_MessageData_ofName(v_mod_2158_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = l_Lean_MessageData_note(v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_msg_2125_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2182_);
v___x_2184_ = v___x_2153_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2187_; 
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_msg_2125_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2188_, lean_object* v_declHint_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2188_, v_declHint_2189_, v___y_2190_);
lean_dec(v___y_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_2193_, lean_object* v_declHint_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2210_; 
v___x_2200_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2193_, v_declHint_2194_, v___y_2198_);
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lean_unknownIdentifierMessageTag;
v___x_2206_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_a_2201_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2206_);
v___x_2208_ = v___x_2203_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_2211_, lean_object* v_declHint_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2211_, v_declHint_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2219_, lean_object* v_msg_2220_, lean_object* v_declHint_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v_a_2228_; lean_object* v___x_2229_; 
v___x_2227_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2220_, v_declHint_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2219_, v_a_2228_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2230_, lean_object* v_msg_2231_, lean_object* v_declHint_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2230_, v_msg_2231_, v_declHint_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v_ref_2230_);
return v_res_2238_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2242_, lean_object* v_constName_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2249_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2250_ = 0;
lean_inc(v_constName_2243_);
v___x_2251_ = l_Lean_MessageData_ofConstName(v_constName_2243_, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2249_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2242_, v___x_2254_, v_constName_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2256_, lean_object* v_constName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2256_, v_constName_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_ref_2256_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(lean_object* v_constName_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_ref_2270_; lean_object* v___x_2271_; 
v_ref_2270_ = lean_ctor_get(v___y_2267_, 5);
v___x_2271_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2270_, v_constName_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(lean_object* v_constName_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v_env_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = lean_st_ref_get(v___y_2283_);
v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_env_2286_);
lean_dec(v___x_2285_);
v___x_2287_ = 0;
lean_inc(v_constName_2279_);
v___x_2288_ = l_Lean_Environment_find_x3f(v_env_2286_, v_constName_2279_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2289_;
}
else
{
lean_object* v_val_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_constName_2279_);
v_val_2290_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2288_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_val_2290_);
lean_dec(v___x_2288_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set_tag(v___x_2292_, 0);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_val_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0___boxed(lean_object* v_constName_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_constName_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(lean_object* v_declName_2305_, lean_object* v_majorPos_x3f_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
lean_inc(v_declName_2305_);
v___x_2312_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_declName_2305_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
lean_inc(v_declName_2305_);
v___x_2314_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_2305_, v_majorPos_x3f_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___f_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref(v___x_2314_);
lean_inc(v_a_2313_);
v___f_2316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2316_, 0, v_declName_2305_);
lean_closure_set(v___f_2316_, 1, v_a_2315_);
lean_closure_set(v___f_2316_, 2, v_a_2313_);
v___x_2317_ = l_Lean_ConstantInfo_type(v_a_2313_);
lean_dec(v_a_2313_);
v___x_2318_ = 0;
v___x_2319_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v___x_2317_, v___f_2316_, v___x_2318_, v___x_2318_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2319_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2313_);
lean_dec(v_declName_2305_);
v_a_2320_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2314_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2314_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_majorPos_x3f_2306_);
lean_dec(v_declName_2305_);
v_a_2328_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2312_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2312_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___boxed(lean_object* v_declName_2336_, lean_object* v_majorPos_x3f_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2336_, v_majorPos_x3f_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(lean_object* v_00_u03b1_2344_, lean_object* v_constName_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2352_, lean_object* v_constName_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(v_00_u03b1_2352_, v_constName_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2360_, lean_object* v_ref_2361_, lean_object* v_constName_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2361_, v_constName_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2369_, lean_object* v_ref_2370_, lean_object* v_constName_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(v_00_u03b1_2369_, v_ref_2370_, v_constName_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v_ref_2370_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2378_, lean_object* v_ref_2379_, lean_object* v_msg_2380_, lean_object* v_declHint_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2379_, v_msg_2380_, v_declHint_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2388_, lean_object* v_ref_2389_, lean_object* v_msg_2390_, lean_object* v_declHint_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2388_, v_ref_2389_, v_msg_2390_, v_declHint_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v_ref_2389_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_2398_, lean_object* v_declHint_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2398_, v_declHint_2399_, v___y_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2406_, lean_object* v_declHint_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2406_, v_declHint_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2414_, lean_object* v_ref_2415_, lean_object* v_msg_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2415_, v_msg_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_ref_2424_, lean_object* v_msg_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2423_, v_ref_2424_, v_msg_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v_ref_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(lean_object* v_msgData_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; lean_object* v_env_2437_; lean_object* v_options_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2436_ = lean_st_ref_get(v___y_2434_);
v_env_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc_ref(v_env_2437_);
lean_dec(v___x_2436_);
v_options_2438_ = lean_ctor_get(v___y_2433_, 2);
v___x_2439_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2440_ = lean_unsigned_to_nat(32u);
v___x_2441_ = lean_mk_empty_array_with_capacity(v___x_2440_);
lean_dec_ref(v___x_2441_);
v___x_2442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2438_);
v___x_2443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2443_, 0, v_env_2437_);
lean_ctor_set(v___x_2443_, 1, v___x_2439_);
lean_ctor_set(v___x_2443_, 2, v___x_2442_);
lean_ctor_set(v___x_2443_, 3, v_options_2438_);
v___x_2444_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_msgData_2432_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msgData_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(lean_object* v_msg_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_ref_2455_; lean_object* v___x_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
v_ref_2455_ = lean_ctor_get(v___y_2452_, 5);
v___x_2456_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msg_2451_, v___y_2452_, v___y_2453_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_inc(v_ref_2455_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_ref_2455_);
lean_ctor_set(v___x_2461_, 1, v_a_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set_tag(v___x_2459_, 1);
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(lean_object* v_ref_2471_, lean_object* v_msg_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_fileName_2476_; lean_object* v_fileMap_2477_; lean_object* v_options_2478_; lean_object* v_currRecDepth_2479_; lean_object* v_maxRecDepth_2480_; lean_object* v_ref_2481_; lean_object* v_currNamespace_2482_; lean_object* v_openDecls_2483_; lean_object* v_initHeartbeats_2484_; lean_object* v_maxHeartbeats_2485_; lean_object* v_quotContext_2486_; lean_object* v_currMacroScope_2487_; uint8_t v_diag_2488_; lean_object* v_cancelTk_x3f_2489_; uint8_t v_suppressElabErrors_2490_; lean_object* v_inheritedTraceOptions_2491_; lean_object* v_ref_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_fileName_2476_ = lean_ctor_get(v___y_2473_, 0);
v_fileMap_2477_ = lean_ctor_get(v___y_2473_, 1);
v_options_2478_ = lean_ctor_get(v___y_2473_, 2);
v_currRecDepth_2479_ = lean_ctor_get(v___y_2473_, 3);
v_maxRecDepth_2480_ = lean_ctor_get(v___y_2473_, 4);
v_ref_2481_ = lean_ctor_get(v___y_2473_, 5);
v_currNamespace_2482_ = lean_ctor_get(v___y_2473_, 6);
v_openDecls_2483_ = lean_ctor_get(v___y_2473_, 7);
v_initHeartbeats_2484_ = lean_ctor_get(v___y_2473_, 8);
v_maxHeartbeats_2485_ = lean_ctor_get(v___y_2473_, 9);
v_quotContext_2486_ = lean_ctor_get(v___y_2473_, 10);
v_currMacroScope_2487_ = lean_ctor_get(v___y_2473_, 11);
v_diag_2488_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*14);
v_cancelTk_x3f_2489_ = lean_ctor_get(v___y_2473_, 12);
v_suppressElabErrors_2490_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2491_ = lean_ctor_get(v___y_2473_, 13);
v_ref_2492_ = l_Lean_replaceRef(v_ref_2471_, v_ref_2481_);
lean_inc_ref(v_inheritedTraceOptions_2491_);
lean_inc(v_cancelTk_x3f_2489_);
lean_inc(v_currMacroScope_2487_);
lean_inc(v_quotContext_2486_);
lean_inc(v_maxHeartbeats_2485_);
lean_inc(v_initHeartbeats_2484_);
lean_inc(v_openDecls_2483_);
lean_inc(v_currNamespace_2482_);
lean_inc(v_maxRecDepth_2480_);
lean_inc(v_currRecDepth_2479_);
lean_inc_ref(v_options_2478_);
lean_inc_ref(v_fileMap_2477_);
lean_inc_ref(v_fileName_2476_);
v___x_2493_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2493_, 0, v_fileName_2476_);
lean_ctor_set(v___x_2493_, 1, v_fileMap_2477_);
lean_ctor_set(v___x_2493_, 2, v_options_2478_);
lean_ctor_set(v___x_2493_, 3, v_currRecDepth_2479_);
lean_ctor_set(v___x_2493_, 4, v_maxRecDepth_2480_);
lean_ctor_set(v___x_2493_, 5, v_ref_2492_);
lean_ctor_set(v___x_2493_, 6, v_currNamespace_2482_);
lean_ctor_set(v___x_2493_, 7, v_openDecls_2483_);
lean_ctor_set(v___x_2493_, 8, v_initHeartbeats_2484_);
lean_ctor_set(v___x_2493_, 9, v_maxHeartbeats_2485_);
lean_ctor_set(v___x_2493_, 10, v_quotContext_2486_);
lean_ctor_set(v___x_2493_, 11, v_currMacroScope_2487_);
lean_ctor_set(v___x_2493_, 12, v_cancelTk_x3f_2489_);
lean_ctor_set(v___x_2493_, 13, v_inheritedTraceOptions_2491_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*14, v_diag_2488_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*14 + 1, v_suppressElabErrors_2490_);
v___x_2494_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2472_, v___x_2493_, v___y_2474_);
lean_dec_ref(v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg___boxed(lean_object* v_ref_2495_, lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2495_, v_msg_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v_ref_2495_);
return v_res_2500_;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7));
v___x_2515_ = l_Lean_stringToMessageData(v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos(lean_object* v_stx_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
lean_inc(v_stx_2516_);
v___x_2520_ = l_Lean_Syntax_getKind(v_stx_2516_);
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4));
v___x_2522_ = lean_name_eq(v___x_2520_, v___x_2521_);
lean_dec(v___x_2520_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_obj_once(&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6, &l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6_once, _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6);
v___x_2524_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_2516_, v___x_2523_, v_a_2517_, v_a_2518_);
lean_dec(v_stx_2516_);
return v___x_2524_;
}
else
{
lean_object* v___x_2525_; lean_object* v___y_2527_; lean_object* v___y_2531_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2525_ = lean_unsigned_to_nat(1u);
v___x_2544_ = l_Lean_Syntax_getArg(v_stx_2516_, v___x_2525_);
v___x_2545_ = l_Lean_Syntax_isNatLit_x3f(v___x_2544_);
lean_dec(v___x_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_unsigned_to_nat(0u);
v___y_2531_ = v___x_2546_;
goto v___jp_2530_;
}
else
{
lean_object* v_val_2547_; 
v_val_2547_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_val_2547_);
lean_dec_ref(v___x_2545_);
v___y_2531_ = v_val_2547_;
goto v___jp_2530_;
}
v___jp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_nat_sub(v___y_2527_, v___x_2525_);
lean_dec(v___y_2527_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
v___jp_2530_:
{
lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = lean_nat_dec_eq(v___y_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_dec(v_stx_2516_);
v___y_2527_ = v___y_2531_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v___y_2531_);
v___x_2534_ = lean_obj_once(&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8, &l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8_once, _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8);
v___x_2535_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_2516_, v___x_2534_, v_a_2517_, v_a_2518_);
lean_dec(v_stx_2516_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(lean_object* v_stx_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(lean_object* v_00_u03b1_2553_, lean_object* v_ref_2554_, lean_object* v_msg_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2554_, v_msg_2555_, v___y_2556_, v___y_2557_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___boxed(lean_object* v_00_u03b1_2560_, lean_object* v_ref_2561_, lean_object* v_msg_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(v_00_u03b1_2560_, v_ref_2561_, v_msg_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v_ref_2561_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(lean_object* v_00_u03b1_2567_, lean_object* v_msg_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_msg_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(v_00_u03b1_2573_, v_msg_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v_x_2579_, lean_object* v_stx_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2580_, v___y_2581_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_x_2585_, lean_object* v_stx_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_x_2585_, v_stx_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v_x_2585_);
return v_res_2590_;
}
}
static uint64_t _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2597_; uint64_t v___x_2598_; 
v___x_2597_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2598_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2597_);
return v___x_2598_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_uint64_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2600_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2601_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set_uint64(v___x_2601_, sizeof(void*)*1, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2602_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2605_ = lean_box(1);
v___x_2606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2607_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2606_);
lean_ctor_set(v___x_2608_, 2, v___x_2605_);
return v___x_2608_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
lean_ctor_set(v___x_2613_, 3, v___x_2612_);
lean_ctor_set(v___x_2613_, 4, v___x_2611_);
lean_ctor_set(v___x_2613_, 5, v___x_2611_);
lean_ctor_set(v___x_2613_, 6, v___x_2611_);
lean_ctor_set(v___x_2613_, 7, v___x_2611_);
lean_ctor_set(v___x_2613_, 8, v___x_2611_);
lean_ctor_set(v___x_2613_, 9, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2615_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
lean_ctor_set(v___x_2615_, 2, v___x_2614_);
lean_ctor_set(v___x_2615_, 3, v___x_2614_);
lean_ctor_set(v___x_2615_, 4, v___x_2614_);
lean_ctor_set(v___x_2615_, 5, v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
lean_ctor_set(v___x_2617_, 2, v___x_2616_);
lean_ctor_set(v___x_2617_, 3, v___x_2616_);
lean_ctor_set(v___x_2617_, 4, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v___x_2618_, lean_object* v_declName_2619_, lean_object* v_majorPos_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
uint8_t v___x_2624_; uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2624_ = 0;
v___x_2625_ = 1;
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2629_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2630_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2631_ = lean_box(0);
lean_inc(v___x_2618_);
v___x_2632_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2632_, 0, v___x_2626_);
lean_ctor_set(v___x_2632_, 1, v___x_2618_);
lean_ctor_set(v___x_2632_, 2, v___x_2629_);
lean_ctor_set(v___x_2632_, 3, v___x_2630_);
lean_ctor_set(v___x_2632_, 4, v___x_2631_);
lean_ctor_set(v___x_2632_, 5, v___x_2627_);
lean_ctor_set(v___x_2632_, 6, v___x_2631_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*7, v___x_2624_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*7 + 1, v___x_2624_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*7 + 2, v___x_2624_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*7 + 3, v___x_2625_);
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2633_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v___x_2618_);
lean_ctor_set(v___x_2636_, 3, v___x_2628_);
lean_ctor_set(v___x_2636_, 4, v___x_2635_);
v___x_2637_ = lean_st_mk_ref(v___x_2636_);
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_majorPos_2620_);
v___x_2639_ = lean_box(0);
v___x_2640_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2619_, v___x_2638_, v___x_2632_, v___x_2637_, v___y_2621_, v___y_2622_);
lean_dec_ref(v___x_2632_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2648_; 
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2640_, 0);
lean_dec(v_unused_2649_);
v___x_2642_ = v___x_2640_;
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v___x_2640_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = lean_st_ref_get(v___x_2637_);
lean_dec(v___x_2637_);
lean_dec(v___x_2644_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2639_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2639_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_dec(v___x_2637_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v___x_2640_, 0);
lean_dec(v_unused_2657_);
v___x_2651_ = v___x_2640_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_dec(v___x_2640_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2639_);
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2639_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_a_2658_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2640_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2640_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v___x_2666_, lean_object* v_declName_2667_, lean_object* v_majorPos_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_2666_, v_declName_2667_, v_majorPos_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
return v_res_2672_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(uint8_t v___x_2673_, lean_object* v_env_2674_, lean_object* v_n_2675_, lean_object* v_x_2676_){
_start:
{
uint8_t v___x_2677_; 
v___x_2677_ = l_Lean_Environment_contains(v_env_2674_, v_n_2675_, v___x_2673_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v___x_2678_, lean_object* v_env_2679_, lean_object* v_n_2680_, lean_object* v_x_2681_){
_start:
{
uint8_t v___x_643__boxed_2682_; uint8_t v_res_2683_; lean_object* v_r_2684_; 
v___x_643__boxed_2682_ = lean_unbox(v___x_2678_);
v_res_2683_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_643__boxed_2682_, v_env_2679_, v_n_2680_, v_x_2681_);
lean_dec(v_x_2681_);
v_r_2684_ = lean_box(v_res_2683_);
return v_r_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2713_ = l_Lean_registerParametricAttribute___redArg(v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object* v_env_2716_, lean_object* v_declName_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = l_Lean_Meta_recursorAttribute;
v___x_2720_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2718_, v___x_2719_, v_env_2716_, v_declName_2717_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo(lean_object* v_declName_2721_, lean_object* v_majorPos_x3f_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_st_ref_get(v_a_2726_);
if (lean_obj_tag(v_majorPos_x3f_2722_) == 0)
{
lean_object* v_env_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_env_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc_ref(v_env_2729_);
lean_dec(v___x_2728_);
lean_inc(v_declName_2721_);
v___x_2730_ = l_Lean_Meta_getMajorPos_x3f(v_env_2729_, v_declName_2721_);
v___x_2731_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2721_, v___x_2730_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; 
lean_dec(v___x_2728_);
v___x_2732_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2721_, v_majorPos_x3f_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo___boxed(lean_object* v_declName_2733_, lean_object* v_majorPos_x3f_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Meta_mkRecursorInfo(v_declName_2733_, v_majorPos_x3f_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
return v_res_2740_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_RecursorInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
