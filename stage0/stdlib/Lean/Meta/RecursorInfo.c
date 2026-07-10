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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
extern lean_object* l_Lean_brecOnSuffix;
extern lean_object* l_Lean_recOnSuffix;
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_6_, 1);
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
lean_dec_ref_known(v_x_39_, 1);
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
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_3249__overap_281_; lean_object* v___x_282_; 
v___x_279_ = lean_box(0);
v___x_280_ = l_instInhabitedOfMonad___redArg(v___x_278_, v___x_279_);
v___x_3249__overap_281_ = lean_panic_fn_borrowed(v___x_280_, v_msg_224_);
lean_dec(v___x_280_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
v___x_282_ = lean_apply_5(v___x_3249__overap_281_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, lean_box(0));
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
lean_dec_ref_known(v___x_380_, 1);
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
lean_dec_ref_known(v_a_394_, 1);
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
lean_object* v___x_431_; lean_object* v_env_432_; uint8_t v___x_433_; uint8_t v___x_434_; 
v___x_431_ = lean_st_ref_get(v_a_423_);
v_env_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_432_);
lean_dec(v___x_431_);
lean_inc(v_declName_418_);
v___x_433_ = l_Lean_isAuxRecursor(v_env_432_, v_declName_418_);
v___x_434_ = lean_bool_not(v___x_433_);
if (v___x_434_ == 0)
{
if (lean_obj_tag(v_declName_418_) == 1)
{
lean_object* v_pre_435_; lean_object* v_str_436_; uint8_t v___y_457_; lean_object* v___x_462_; uint8_t v___x_463_; uint8_t v___x_464_; 
v_pre_435_ = lean_ctor_get(v_declName_418_, 0);
lean_inc(v_pre_435_);
v_str_436_ = lean_ctor_get(v_declName_418_, 1);
lean_inc_ref(v_str_436_);
lean_dec_ref_known(v_declName_418_, 2);
v___x_462_ = l_Lean_recOnSuffix;
v___x_463_ = lean_string_dec_eq(v_str_436_, v___x_462_);
v___x_464_ = lean_bool_not(v___x_463_);
if (v___x_464_ == 0)
{
v___y_457_ = v___x_464_;
goto v___jp_456_;
}
else
{
lean_object* v___x_465_; uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_465_ = l_Lean_casesOnSuffix;
v___x_466_ = lean_string_dec_eq(v_str_436_, v___x_465_);
v___x_467_ = lean_bool_not(v___x_466_);
v___y_457_ = v___x_467_;
goto v___jp_456_;
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
lean_dec_ref_known(v___x_439_, 1);
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
v___jp_456_:
{
if (v___y_457_ == 0)
{
goto v___jp_437_;
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_458_ = l_Lean_brecOnSuffix;
v___x_459_ = lean_string_dec_eq(v_str_436_, v___x_458_);
v___x_460_ = lean_bool_not(v___x_459_);
if (v___x_460_ == 0)
{
goto v___jp_437_;
}
else
{
lean_object* v___x_461_; 
lean_dec_ref(v_str_436_);
lean_dec(v_pre_435_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_majorPos_x3f_419_);
return v___x_461_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_declName_418_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v_majorPos_x3f_419_);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v_declName_418_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_majorPos_x3f_419_);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_declName_418_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_majorPos_x3f_419_);
return v___x_470_;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(lean_object* v_00_u03b1_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(v_00_u03b1_487_, v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
v___x_500_ = l_Lean_Expr_isFVar(v___x_499_);
v___x_501_ = lean_bool_not(v___x_500_);
if (v___x_501_ == 0)
{
size_t v___x_502_; size_t v___x_503_; 
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_496_, v___x_502_);
v_i_496_ = v___x_503_;
goto _start;
}
else
{
return v___x_501_;
}
}
else
{
uint8_t v___x_505_; 
v___x_505_ = 0;
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0___boxed(lean_object* v_as_506_, lean_object* v_i_507_, lean_object* v_stop_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; uint8_t v_res_511_; lean_object* v_r_512_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_508_);
lean_dec(v_stop_508_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v_as_506_, v_i_boxed_509_, v_stop_boxed_510_);
lean_dec_ref(v_as_506_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(lean_object* v_declName_519_, lean_object* v_motive_520_, lean_object* v_motiveArgs_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
uint8_t v___y_528_; uint8_t v___x_537_; 
v___x_537_ = l_Lean_Expr_isFVar(v_motive_520_);
if (v___x_537_ == 0)
{
v___y_528_ = v___x_537_;
goto v___jp_527_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_motiveArgs_521_);
v___x_540_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_bool_not(v___x_540_);
v___y_528_ = v___x_541_;
goto v___jp_527_;
}
else
{
if (v___x_540_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = lean_bool_not(v___x_540_);
v___y_528_ = v___x_542_;
goto v___jp_527_;
}
else
{
size_t v___x_543_; size_t v___x_544_; uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_543_ = ((size_t)0ULL);
v___x_544_ = lean_usize_of_nat(v___x_539_);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v_motiveArgs_521_, v___x_543_, v___x_544_);
v___x_546_ = lean_bool_not(v___x_545_);
v___y_528_ = v___x_546_;
goto v___jp_527_;
}
}
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_530_ = l_Lean_MessageData_ofConstName(v_declName_519_, v___y_528_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_533_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_declName_519_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(lean_object* v_declName_547_, lean_object* v_motive_548_, lean_object* v_motiveArgs_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_547_, v_motive_548_, v_motiveArgs_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec_ref(v_motiveArgs_549_);
lean_dec_ref(v_motive_548_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(lean_object* v_xs_556_, lean_object* v_motive_557_, lean_object* v_i_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_xs_556_);
v___x_560_ = lean_nat_dec_lt(v_i_558_, v___x_559_);
if (v___x_560_ == 0)
{
return v_i_558_;
}
else
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_fget_borrowed(v_xs_556_, v_i_558_);
v___x_562_ = lean_expr_eqv(v_motive_557_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_i_558_, v___x_563_);
lean_dec(v_i_558_);
v_i_558_ = v___x_564_;
goto _start;
}
else
{
return v_i_558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(lean_object* v_xs_566_, lean_object* v_motive_567_, lean_object* v_i_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(v_xs_566_, v_motive_567_, v_i_568_);
lean_dec_ref(v_motive_567_);
lean_dec_ref(v_xs_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(lean_object* v_xs_570_, lean_object* v_v_571_, lean_object* v_i_572_){
_start:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_xs_570_);
v___x_574_ = lean_nat_dec_lt(v_i_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v_i_572_);
v___x_575_ = lean_box(0);
return v___x_575_;
}
else
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_array_fget_borrowed(v_xs_570_, v_i_572_);
v___x_577_ = lean_expr_eqv(v___x_576_, v_v_571_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_i_572_, v___x_578_);
lean_dec(v_i_572_);
v_i_572_ = v___x_579_;
goto _start;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_i_572_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_582_, lean_object* v_v_583_, lean_object* v_i_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_582_, v_v_583_, v_i_584_);
lean_dec_ref(v_v_583_);
lean_dec_ref(v_xs_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(lean_object* v_xs_586_, lean_object* v_v_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_586_, v_v_587_, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0___boxed(lean_object* v_xs_590_, lean_object* v_v_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_590_, v_v_591_);
lean_dec_ref(v_v_591_);
lean_dec_ref(v_xs_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(lean_object* v_xs_593_, lean_object* v_v_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_593_, v_v_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_box(0);
return v___x_596_;
}
else
{
lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_val_597_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_val_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0___boxed(lean_object* v_xs_605_, lean_object* v_v_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_605_, v_v_606_);
lean_dec_ref(v_v_606_);
lean_dec_ref(v_xs_605_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(lean_object* v_a_608_, lean_object* v_as_609_, size_t v_i_610_, size_t v_stop_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = lean_usize_dec_eq(v_i_610_, v_stop_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_uget_borrowed(v_as_609_, v_i_610_);
v___x_614_ = lean_expr_eqv(v_a_608_, v___x_613_);
if (v___x_614_ == 0)
{
size_t v___x_615_; size_t v___x_616_; 
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_add(v_i_610_, v___x_615_);
v_i_610_ = v___x_616_;
goto _start;
}
else
{
return v___x_614_;
}
}
else
{
uint8_t v___x_618_; 
v___x_618_ = 0;
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2___boxed(lean_object* v_a_619_, lean_object* v_as_620_, lean_object* v_i_621_, lean_object* v_stop_622_){
_start:
{
size_t v_i_boxed_623_; size_t v_stop_boxed_624_; uint8_t v_res_625_; lean_object* v_r_626_; 
v_i_boxed_623_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_stop_boxed_624_ = lean_unbox_usize(v_stop_622_);
lean_dec(v_stop_622_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_619_, v_as_620_, v_i_boxed_623_, v_stop_boxed_624_);
lean_dec_ref(v_as_620_);
lean_dec_ref(v_a_619_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(lean_object* v_as_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_array_get_size(v_as_627_);
v___x_631_ = lean_nat_dec_lt(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_630_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_628_, v_as_627_, v___x_632_, v___x_633_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1___boxed(lean_object* v_as_635_, lean_object* v_a_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_as_635_, v_a_636_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_as_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(lean_object* v_declName_654_, lean_object* v_majorPos_x3f_655_, lean_object* v_xs_656_, lean_object* v_motiveArgs_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
if (lean_obj_tag(v_majorPos_x3f_655_) == 0)
{
lean_object* v___x_663_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_663_ = l_Lean_instInhabitedExpr;
v___x_693_ = lean_array_get_size(v_motiveArgs_657_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_nat_dec_eq(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
v___y_665_ = v_a_658_;
v___y_666_ = v_a_659_;
v___y_667_ = v_a_660_;
v___y_668_ = v_a_661_;
goto v___jp_664_;
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v___x_696_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3);
v___x_697_ = 0;
v___x_698_ = l_Lean_MessageData_ofConstName(v_declName_654_, v___x_697_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_696_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_701_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
v___jp_664_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_major_672_; lean_object* v___x_673_; 
v___x_669_ = lean_array_get_size(v_motiveArgs_657_);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_sub(v___x_669_, v___x_670_);
v_major_672_ = lean_array_get_borrowed(v___x_663_, v_motiveArgs_657_, v___x_671_);
lean_dec(v___x_671_);
v___x_673_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_656_, v_major_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_674_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1);
v___x_675_ = 0;
v___x_676_ = l_Lean_MessageData_ofConstName(v_declName_654_, v___x_675_);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_674_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_679_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_680_;
}
else
{
lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_692_; 
lean_dec(v_declName_654_);
v_val_681_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_692_ == 0)
{
v___x_683_ = v___x_673_;
v_isShared_684_ = v_isSharedCheck_692_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_dec(v___x_673_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_692_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_685_ = 1;
v___x_686_ = lean_box(v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_val_681_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
lean_inc(v_major_672_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_major_672_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 0);
lean_ctor_set(v___x_683_, 0, v___x_688_);
v___x_690_ = v___x_683_;
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
}
}
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_declName_654_);
v_val_711_ = lean_ctor_get(v_majorPos_x3f_655_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_majorPos_x3f_655_);
if (v_isSharedCheck_735_ == 0)
{
v___x_713_ = v_majorPos_x3f_655_;
v_isShared_714_ = v_isSharedCheck_735_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_val_711_);
lean_dec(v_majorPos_x3f_655_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_735_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = lean_array_get_size(v_xs_656_);
v___x_716_ = lean_nat_dec_lt(v_val_711_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec(v_val_711_);
v___x_717_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7);
v___x_718_ = l_Nat_reprFast(v___x_715_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 3);
lean_ctor_set(v___x_713_, 0, v___x_718_);
v___x_720_ = v___x_713_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_726_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_721_ = l_Lean_MessageData_ofFormat(v___x_720_);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_717_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_724_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
return v___x_725_;
}
}
else
{
lean_object* v_major_727_; uint8_t v_depElim_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_major_727_ = lean_array_fget_borrowed(v_xs_656_, v_val_711_);
v_depElim_728_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_motiveArgs_657_, v_major_727_);
v___x_729_ = lean_box(v_depElim_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_val_711_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
lean_inc(v_major_727_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_major_727_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 0);
lean_ctor_set(v___x_713_, 0, v___x_731_);
v___x_733_ = v___x_713_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(lean_object* v_declName_736_, lean_object* v_majorPos_x3f_737_, lean_object* v_xs_738_, lean_object* v_motiveArgs_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_736_, v_majorPos_x3f_737_, v_xs_738_, v_motiveArgs_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec_ref(v_motiveArgs_739_);
lean_dec_ref(v_xs_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(lean_object* v___x_746_, lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v___x_746_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_750_);
return v___x_757_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_array_uget_borrowed(v_as_747_, v_i_749_);
lean_inc_ref(v___x_746_);
lean_inc(v_a_758_);
v___x_759_ = l_Lean_Meta_isExprDefEq(v_a_758_, v___x_746_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_794_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_794_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_794_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_794_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; 
v___x_764_ = lean_unbox(v_a_760_);
lean_dec(v_a_760_);
if (v___x_764_ == 0)
{
lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_762_);
v_snd_765_ = lean_ctor_get(v_b_750_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_b_750_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_b_750_, 0);
lean_dec(v_unused_779_);
v___x_767_ = v_b_750_;
v_isShared_768_ = v_isSharedCheck_778_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_dec(v_b_750_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_778_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_769_ = lean_box(0);
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_add(v_snd_765_, v___x_770_);
lean_dec(v_snd_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_771_);
lean_ctor_set(v___x_767_, 0, v___x_769_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_749_, v___x_774_);
v_i_749_ = v___x_775_;
v_b_750_ = v___x_773_;
goto _start;
}
}
}
else
{
lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v___x_746_);
v_snd_780_ = lean_ctor_get(v_b_750_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_b_750_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_b_750_, 0);
lean_dec(v_unused_793_);
v___x_782_ = v_b_750_;
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_dec(v_b_750_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_inc(v_snd_780_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_snd_780_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_snd_780_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_787_);
v___x_789_ = v___x_762_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_b_750_);
lean_dec_ref(v___x_746_);
v_a_795_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_759_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_759_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0___boxed(lean_object* v___x_803_, lean_object* v_as_804_, lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_b_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
size_t v_sz_boxed_813_; size_t v_i_boxed_814_; lean_object* v_res_815_; 
v_sz_boxed_813_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_814_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_803_, v_as_804_, v_sz_boxed_813_, v_i_boxed_814_, v_b_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v_as_804_);
return v_res_815_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(lean_object* v_upperBound_822_, lean_object* v_xs_823_, lean_object* v_declName_824_, lean_object* v_Iargs_825_, lean_object* v_a_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_a_834_; uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_lt(v_a_826_, v_upperBound_822_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v_a_826_);
lean_dec(v_declName_824_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v_b_827_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_a_843_; lean_object* v___x_872_; lean_object* v___x_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_840_ = l_Lean_instInhabitedExpr;
v___x_841_ = lean_array_get_borrowed(v___x_840_, v_xs_823_, v_a_826_);
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2));
v_sz_874_ = lean_array_size(v_Iargs_825_);
v___x_875_ = ((size_t)0ULL);
lean_inc(v___x_841_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_841_, v_Iargs_825_, v_sz_874_, v___x_875_, v___x_873_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v_fst_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v_fst_878_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_fst_878_);
lean_dec(v_a_877_);
if (lean_obj_tag(v_fst_878_) == 0)
{
v_a_843_ = v___x_872_;
goto v___jp_842_;
}
else
{
lean_object* v_val_879_; 
v_val_879_ = lean_ctor_get(v_fst_878_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_fst_878_, 1);
if (lean_obj_tag(v_val_879_) == 0)
{
v_a_843_ = v_val_879_;
goto v___jp_842_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = lean_array_push(v_b_827_, v_val_879_);
v_a_834_ = v___x_880_;
goto v___jp_833_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_b_827_);
lean_dec(v_a_826_);
lean_dec(v_declName_824_);
v_a_881_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_876_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
v___jp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = l_Lean_Expr_fvarId_x21(v___x_841_);
v___x_845_ = l_Lean_FVarId_getDecl___redArg(v___x_844_, v___y_828_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; uint8_t v___x_847_; uint8_t v___x_848_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = l_Lean_LocalDecl_binderInfo(v_a_846_);
lean_dec(v_a_846_);
v___x_848_ = l_Lean_BinderInfo_isInstImplicit(v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v_a_843_);
v___x_849_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
lean_inc(v_declName_824_);
v___x_850_ = l_Lean_MessageData_ofConstName(v_declName_824_, v___x_848_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_853_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_dec_ref_known(v___x_854_, 1);
v_a_834_ = v_b_827_;
goto v___jp_833_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_b_827_);
lean_dec(v_a_826_);
lean_dec(v_declName_824_);
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_array_push(v_b_827_, v_a_843_);
v_a_834_ = v___x_863_;
goto v___jp_833_;
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_843_);
lean_dec_ref(v_b_827_);
lean_dec(v_a_826_);
lean_dec(v_declName_824_);
v_a_864_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_845_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_845_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_add(v_a_826_, v___x_835_);
lean_dec(v_a_826_);
v_a_826_ = v___x_836_;
v_b_827_ = v_a_834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___boxed(lean_object* v_upperBound_889_, lean_object* v_xs_890_, lean_object* v_declName_891_, lean_object* v_Iargs_892_, lean_object* v_a_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_889_, v_xs_890_, v_declName_891_, v_Iargs_892_, v_a_893_, v_b_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_Iargs_892_);
lean_dec_ref(v_xs_890_);
lean_dec(v_upperBound_889_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(lean_object* v_declName_903_, lean_object* v_xs_904_, lean_object* v_numParams_905_, lean_object* v_Iargs_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; lean_object* v_paramsPos_913_; lean_object* v___x_914_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v_paramsPos_913_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0));
v___x_914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_numParams_905_, v_xs_904_, v_declName_903_, v_Iargs_906_, v___x_912_, v_paramsPos_913_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_array_to_list(v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_914_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_914_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(lean_object* v_declName_932_, lean_object* v_xs_933_, lean_object* v_numParams_934_, lean_object* v_Iargs_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_932_, v_xs_933_, v_numParams_934_, v_Iargs_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec_ref(v_Iargs_935_);
lean_dec(v_numParams_934_);
lean_dec_ref(v_xs_933_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(lean_object* v_upperBound_942_, lean_object* v_xs_943_, lean_object* v_declName_944_, lean_object* v_Iargs_945_, lean_object* v_inst_946_, lean_object* v_R_947_, lean_object* v_a_948_, lean_object* v_b_949_, lean_object* v_c_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_942_, v_xs_943_, v_declName_944_, v_Iargs_945_, v_a_948_, v_b_949_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___boxed(lean_object* v_upperBound_957_, lean_object* v_xs_958_, lean_object* v_declName_959_, lean_object* v_Iargs_960_, lean_object* v_inst_961_, lean_object* v_R_962_, lean_object* v_a_963_, lean_object* v_b_964_, lean_object* v_c_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(v_upperBound_957_, v_xs_958_, v_declName_959_, v_Iargs_960_, v_inst_961_, v_R_962_, v_a_963_, v_b_964_, v_c_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_Iargs_960_);
lean_dec_ref(v_xs_958_);
lean_dec(v_upperBound_957_);
return v_res_971_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(lean_object* v_declName_975_, lean_object* v_upperBound_976_, lean_object* v_majorPos_977_, lean_object* v_numIndices_978_, lean_object* v_xs_979_, lean_object* v_Iargs_980_, lean_object* v_a_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_a_989_; uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_lt(v_a_981_, v_upperBound_976_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
lean_dec(v_a_981_);
lean_dec(v_declName_975_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_b_982_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; size_t v_sz_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1011_ = l_Lean_instInhabitedExpr;
v___x_1012_ = lean_nat_sub(v_majorPos_977_, v_numIndices_978_);
v___x_1013_ = lean_nat_add(v___x_1012_, v_a_981_);
lean_dec(v___x_1012_);
v___x_1014_ = lean_array_get_borrowed(v___x_1011_, v_xs_979_, v___x_1013_);
lean_dec(v___x_1013_);
v___x_1015_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2));
v_sz_1016_ = lean_array_size(v_Iargs_980_);
v___x_1017_ = ((size_t)0ULL);
lean_inc(v___x_1014_);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_1014_, v_Iargs_980_, v_sz_1016_, v___x_1017_, v___x_1015_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_fst_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_fst_1020_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_fst_1020_);
lean_dec(v_a_1019_);
if (lean_obj_tag(v_fst_1020_) == 0)
{
goto v___jp_993_;
}
else
{
lean_object* v_val_1021_; 
v_val_1021_ = lean_ctor_get(v_fst_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v_fst_1020_, 1);
if (lean_obj_tag(v_val_1021_) == 0)
{
goto v___jp_993_;
}
else
{
lean_object* v_val_1022_; lean_object* v___x_1023_; 
v_val_1022_ = lean_ctor_get(v_val_1021_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v_val_1021_, 1);
v___x_1023_ = lean_array_push(v_b_982_, v_val_1022_);
v_a_989_ = v___x_1023_;
goto v___jp_988_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_b_982_);
lean_dec(v_a_981_);
lean_dec(v_declName_975_);
v_a_1024_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1018_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
v___jp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_a_981_, v___x_990_);
lean_dec(v_a_981_);
v_a_981_ = v___x_991_;
v_b_982_ = v_a_989_;
goto _start;
}
v___jp_993_:
{
lean_object* v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_994_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_995_ = 0;
lean_inc(v_declName_975_);
v___x_996_ = l_Lean_MessageData_ofConstName(v_declName_975_, v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_994_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_999_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_dec_ref_known(v___x_1000_, 1);
v_a_989_ = v_b_982_;
goto v___jp_988_;
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_b_982_);
lean_dec(v_a_981_);
lean_dec(v_declName_975_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___boxed(lean_object* v_declName_1032_, lean_object* v_upperBound_1033_, lean_object* v_majorPos_1034_, lean_object* v_numIndices_1035_, lean_object* v_xs_1036_, lean_object* v_Iargs_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1032_, v_upperBound_1033_, v_majorPos_1034_, v_numIndices_1035_, v_xs_1036_, v_Iargs_1037_, v_a_1038_, v_b_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec_ref(v_Iargs_1037_);
lean_dec_ref(v_xs_1036_);
lean_dec(v_numIndices_1035_);
lean_dec(v_majorPos_1034_);
lean_dec(v_upperBound_1033_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(lean_object* v_declName_1048_, lean_object* v_xs_1049_, lean_object* v_majorPos_1050_, lean_object* v_numIndices_1051_, lean_object* v_Iargs_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v_indicesPos_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v_indicesPos_1059_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0));
v___x_1060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1048_, v_numIndices_1051_, v_majorPos_1050_, v_numIndices_1051_, v_xs_1049_, v_Iargs_1052_, v___x_1058_, v_indicesPos_1059_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_array_to_list(v_a_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_a_1070_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1060_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1060_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(lean_object* v_declName_1078_, lean_object* v_xs_1079_, lean_object* v_majorPos_1080_, lean_object* v_numIndices_1081_, lean_object* v_Iargs_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1078_, v_xs_1079_, v_majorPos_1080_, v_numIndices_1081_, v_Iargs_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec_ref(v_Iargs_1082_);
lean_dec(v_numIndices_1081_);
lean_dec(v_majorPos_1080_);
lean_dec_ref(v_xs_1079_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(lean_object* v_declName_1089_, lean_object* v_upperBound_1090_, lean_object* v_majorPos_1091_, lean_object* v_numIndices_1092_, lean_object* v_xs_1093_, lean_object* v_Iargs_1094_, lean_object* v_inst_1095_, lean_object* v_R_1096_, lean_object* v_a_1097_, lean_object* v_b_1098_, lean_object* v_c_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_1089_, v_upperBound_1090_, v_majorPos_1091_, v_numIndices_1092_, v_xs_1093_, v_Iargs_1094_, v_a_1097_, v_b_1098_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___boxed(lean_object* v_declName_1106_, lean_object* v_upperBound_1107_, lean_object* v_majorPos_1108_, lean_object* v_numIndices_1109_, lean_object* v_xs_1110_, lean_object* v_Iargs_1111_, lean_object* v_inst_1112_, lean_object* v_R_1113_, lean_object* v_a_1114_, lean_object* v_b_1115_, lean_object* v_c_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(v_declName_1106_, v_upperBound_1107_, v_majorPos_1108_, v_numIndices_1109_, v_xs_1110_, v_Iargs_1111_, v_inst_1112_, v_R_1113_, v_a_1114_, v_b_1115_, v_c_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec_ref(v_Iargs_1111_);
lean_dec_ref(v_xs_1110_);
lean_dec(v_numIndices_1109_);
lean_dec(v_majorPos_1108_);
lean_dec(v_upperBound_1107_);
return v_res_1122_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(lean_object* v_declName_1126_, lean_object* v_motiveResultType_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; 
if (lean_obj_tag(v_motiveResultType_1127_) == 3)
{
lean_object* v_u_1145_; 
v_u_1145_ = lean_ctor_get(v_motiveResultType_1127_, 0);
switch(lean_obj_tag(v_u_1145_))
{
case 0:
{
lean_object* v___x_1146_; 
lean_dec(v_declName_1126_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_u_1145_);
return v___x_1146_;
}
case 4:
{
lean_object* v___x_1147_; 
lean_dec(v_declName_1126_);
lean_inc_ref(v_u_1145_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_u_1145_);
return v___x_1147_;
}
default: 
{
v___y_1134_ = v_a_1128_;
v___y_1135_ = v_a_1129_;
v___y_1136_ = v_a_1130_;
v___y_1137_ = v_a_1131_;
goto v___jp_1133_;
}
}
}
else
{
v___y_1134_ = v_a_1128_;
v___y_1135_ = v_a_1129_;
v___y_1136_ = v_a_1130_;
v___y_1137_ = v_a_1131_;
goto v___jp_1133_;
}
v___jp_1133_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1138_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1139_ = 0;
v___x_1140_ = l_Lean_MessageData_ofConstName(v_declName_1126_, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1138_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1143_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(lean_object* v_declName_1148_, lean_object* v_motiveResultType_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1148_, v_motiveResultType_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec_ref(v_motiveResultType_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(lean_object* v___x_1156_, lean_object* v_as_1157_, lean_object* v_j_1158_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_array_get_size(v_as_1157_);
v___x_1160_ = lean_nat_dec_lt(v_j_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_j_1158_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_array_fget_borrowed(v_as_1157_, v_j_1158_);
v___x_1163_ = lean_level_eq(v___x_1162_, v___x_1156_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_j_1158_, v___x_1164_);
lean_dec(v_j_1158_);
v_j_1158_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_j_1158_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0___boxed(lean_object* v___x_1168_, lean_object* v_as_1169_, lean_object* v_j_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_1168_, v_as_1169_, v_j_1170_);
lean_dec_ref(v_as_1169_);
lean_dec(v___x_1168_);
return v_res_1171_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(lean_object* v_motiveLvl_1175_, lean_object* v_Ilevels_1176_, lean_object* v_declName_1177_, lean_object* v_as_x27_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
if (lean_obj_tag(v_as_x27_1178_) == 0)
{
lean_object* v___x_1185_; 
lean_dec(v_declName_1177_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_b_1179_);
return v___x_1185_;
}
else
{
lean_object* v_head_1186_; lean_object* v_tail_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_head_1186_ = lean_ctor_get(v_as_x27_1178_, 0);
v_tail_1187_ = lean_ctor_get(v_as_x27_1178_, 1);
lean_inc(v_head_1186_);
v___x_1188_ = l_Lean_mkLevelParam(v_head_1186_);
v___x_1189_ = lean_level_eq(v_motiveLvl_1175_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_1188_, v_Ilevels_1176_, v___x_1190_);
lean_dec(v___x_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_b_1179_);
v___x_1192_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1193_ = l_Lean_MessageData_ofConstName(v_declName_1177_, v___x_1189_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
lean_inc(v_head_1186_);
v___x_1197_ = l_Lean_MessageData_ofName(v_head_1186_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1200_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_object* v_val_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1219_; 
v_val_1210_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1212_ = v___x_1191_;
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_val_1210_);
lean_dec(v___x_1191_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_val_1210_);
v___x_1215_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_array_push(v_b_1179_, v___x_1215_);
v_as_x27_1178_ = v_tail_1187_;
v_b_1179_ = v___x_1216_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec(v___x_1188_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_array_push(v_b_1179_, v___x_1220_);
v_as_x27_1178_ = v_tail_1187_;
v_b_1179_ = v___x_1221_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___boxed(lean_object* v_motiveLvl_1223_, lean_object* v_Ilevels_1224_, lean_object* v_declName_1225_, lean_object* v_as_x27_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1223_, v_Ilevels_1224_, v_declName_1225_, v_as_x27_1226_, v_b_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v_as_x27_1226_);
lean_dec_ref(v_Ilevels_1224_);
lean_dec(v_motiveLvl_1223_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(lean_object* v_declName_1236_, lean_object* v_lparams_1237_, lean_object* v_motiveLvl_1238_, lean_object* v_Ilevels_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_Ilevels_1245_; lean_object* v_univLevelPos_1246_; lean_object* v___x_1247_; 
v_Ilevels_1245_ = lean_array_mk(v_Ilevels_1239_);
v_univLevelPos_1246_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0));
v___x_1247_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1238_, v_Ilevels_1245_, v_declName_1236_, v_lparams_1237_, v_univLevelPos_1246_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec_ref(v_Ilevels_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1256_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_array_to_list(v_a_1248_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1247_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1247_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(lean_object* v_declName_1265_, lean_object* v_lparams_1266_, lean_object* v_motiveLvl_1267_, lean_object* v_Ilevels_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1265_, v_lparams_1266_, v_motiveLvl_1267_, v_Ilevels_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_motiveLvl_1267_);
lean_dec(v_lparams_1266_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(lean_object* v_motiveLvl_1275_, lean_object* v_Ilevels_1276_, lean_object* v_declName_1277_, lean_object* v_as_1278_, lean_object* v_as_x27_1279_, lean_object* v_b_1280_, lean_object* v_a_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_1275_, v_Ilevels_1276_, v_declName_1277_, v_as_x27_1279_, v_b_1280_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___boxed(lean_object* v_motiveLvl_1288_, lean_object* v_Ilevels_1289_, lean_object* v_declName_1290_, lean_object* v_as_1291_, lean_object* v_as_x27_1292_, lean_object* v_b_1293_, lean_object* v_a_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(v_motiveLvl_1288_, v_Ilevels_1289_, v_declName_1290_, v_as_1291_, v_as_x27_1292_, v_b_1293_, v_a_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v_as_x27_1292_);
lean_dec(v_as_1291_);
lean_dec_ref(v_Ilevels_1289_);
lean_dec(v_motiveLvl_1288_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(lean_object* v_k_1301_, lean_object* v_b_1302_, lean_object* v_c_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
v___x_1309_ = lean_apply_7(v_k_1301_, v_b_1302_, v_c_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed(lean_object* v_k_1310_, lean_object* v_b_1311_, lean_object* v_c_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(v_k_1310_, v_b_1311_, v_c_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(lean_object* v_type_1319_, lean_object* v_k_1320_, uint8_t v_cleanupAnnotations_1321_, uint8_t v_whnfType_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___f_1328_; lean_object* v___x_1329_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1328_, 0, v_k_1320_);
v___x_1329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1319_, v___f_1328_, v_cleanupAnnotations_1321_, v_whnfType_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1329_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1329_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___boxed(lean_object* v_type_1346_, lean_object* v_k_1347_, lean_object* v_cleanupAnnotations_1348_, lean_object* v_whnfType_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1355_; uint8_t v_whnfType_boxed_1356_; lean_object* v_res_1357_; 
v_cleanupAnnotations_boxed_1355_ = lean_unbox(v_cleanupAnnotations_1348_);
v_whnfType_boxed_1356_ = lean_unbox(v_whnfType_1349_);
v_res_1357_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1346_, v_k_1347_, v_cleanupAnnotations_boxed_1355_, v_whnfType_boxed_1356_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(lean_object* v_00_u03b1_1358_, lean_object* v_type_1359_, lean_object* v_k_1360_, uint8_t v_cleanupAnnotations_1361_, uint8_t v_whnfType_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_1359_, v_k_1360_, v_cleanupAnnotations_1361_, v_whnfType_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_type_1370_, lean_object* v_k_1371_, lean_object* v_cleanupAnnotations_1372_, lean_object* v_whnfType_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1379_; uint8_t v_whnfType_boxed_1380_; lean_object* v_res_1381_; 
v_cleanupAnnotations_boxed_1379_ = lean_unbox(v_cleanupAnnotations_1372_);
v_whnfType_boxed_1380_ = lean_unbox(v_whnfType_1373_);
v_res_1381_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(v_00_u03b1_1369_, v_type_1370_, v_k_1371_, v_cleanupAnnotations_boxed_1379_, v_whnfType_boxed_1380_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1381_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(lean_object* v_motive_1382_, lean_object* v_e_1383_){
_start:
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_expr_eqv(v_e_1383_, v_motive_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed(lean_object* v_motive_1385_, lean_object* v_e_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(v_motive_1385_, v_e_1386_);
lean_dec_ref(v_e_1386_);
lean_dec_ref(v_motive_1385_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(lean_object* v_motive_1389_, uint8_t v___x_1390_, lean_object* v_as_1391_, size_t v_i_1392_, size_t v_stop_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_eq(v_i_1392_, v_stop_1393_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_array_uget_borrowed(v_as_1391_, v_i_1392_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___x_1400_);
v___x_1401_ = lean_infer_type(v___x_1400_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1420_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1420_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1420_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___f_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
lean_inc_ref(v_motive_1389_);
v___f_1406_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1406_, 0, v_motive_1389_);
v___x_1407_ = 1;
v___x_1408_ = lean_find_expr(v___f_1406_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v___f_1406_);
if (lean_obj_tag(v___x_1408_) == 0)
{
if (v___x_1390_ == 0)
{
size_t v___x_1409_; size_t v___x_1410_; 
lean_del_object(v___x_1404_);
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1392_, v___x_1409_);
v_i_1392_ = v___x_1410_;
goto _start;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec_ref(v_motive_1389_);
v___x_1412_ = lean_box(v___x_1407_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec_ref_known(v___x_1408_, 1);
lean_dec_ref(v_motive_1389_);
v___x_1416_ = lean_box(v___x_1407_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1416_);
v___x_1418_ = v___x_1404_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v_motive_1389_);
v_a_1421_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1401_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1401_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_motive_1389_);
v___x_1429_ = 0;
v___x_1430_ = lean_box(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___boxed(lean_object* v_motive_1432_, lean_object* v___x_1433_, lean_object* v_as_1434_, lean_object* v_i_1435_, lean_object* v_stop_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v___x_4143__boxed_1442_; size_t v_i_boxed_1443_; size_t v_stop_boxed_1444_; lean_object* v_res_1445_; 
v___x_4143__boxed_1442_ = lean_unbox(v___x_1433_);
v_i_boxed_1443_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_stop_boxed_1444_ = lean_unbox_usize(v_stop_1436_);
lean_dec(v_stop_1436_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1432_, v___x_4143__boxed_1442_, v_as_1434_, v_i_boxed_1443_, v_stop_boxed_1444_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_as_1434_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(lean_object* v_motive_1446_, lean_object* v___x_1447_, uint8_t v___x_1448_, lean_object* v_minorArgs_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 5)
{
lean_object* v_fn_1458_; lean_object* v_arg_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_fn_1458_ = lean_ctor_get(v_x_1450_, 0);
lean_inc_ref(v_fn_1458_);
v_arg_1459_ = lean_ctor_get(v_x_1450_, 1);
lean_inc_ref(v_arg_1459_);
lean_dec_ref_known(v_x_1450_, 2);
v___x_1460_ = lean_array_set(v_x_1451_, v_x_1452_, v_arg_1459_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_sub(v_x_1452_, v___x_1461_);
lean_dec(v_x_1452_);
v_x_1450_ = v_fn_1458_;
v_x_1451_ = v___x_1460_;
v_x_1452_ = v___x_1462_;
goto _start;
}
else
{
uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v_recursor_1468_; 
lean_dec(v_x_1452_);
lean_dec_ref(v_x_1451_);
v___x_1464_ = lean_expr_eqv(v_x_1450_, v_motive_1446_);
lean_dec_ref(v_x_1450_);
v___x_1465_ = lean_box(v___x_1464_);
v___x_1466_ = lean_array_push(v___x_1447_, v___x_1465_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_array_get_size(v_minorArgs_1449_);
v___x_1474_ = lean_nat_dec_lt(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_dec_ref(v_motive_1446_);
v_recursor_1468_ = v___x_1448_;
goto v___jp_1467_;
}
else
{
if (v___x_1474_ == 0)
{
lean_dec_ref(v_motive_1446_);
v_recursor_1468_ = v___x_1448_;
goto v___jp_1467_;
}
else
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = lean_usize_of_nat(v___x_1473_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_1446_, v___x_1448_, v_minorArgs_1449_, v___x_1475_, v___x_1476_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; uint8_t v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_unbox(v_a_1478_);
lean_dec(v_a_1478_);
v_recursor_1468_ = v___x_1479_;
goto v___jp_1467_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___x_1466_);
v_a_1480_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1477_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1477_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_motive_1446_);
v_recursor_1468_ = v___x_1448_;
goto v___jp_1467_;
}
v___jp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_box(v_recursor_1468_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1466_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1___boxed(lean_object* v_motive_1488_, lean_object* v___x_1489_, lean_object* v___x_1490_, lean_object* v_minorArgs_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_4229__boxed_1500_; lean_object* v_res_1501_; 
v___x_4229__boxed_1500_ = lean_unbox(v___x_1490_);
v_res_1501_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1488_, v___x_1489_, v___x_4229__boxed_1500_, v_minorArgs_1491_, v_x_1492_, v_x_1493_, v_x_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v_minorArgs_1491_);
return v_res_1501_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1502_; lean_object* v_dummy_1503_; 
v___x_1502_ = lean_box(0);
v_dummy_1503_ = l_Lean_Expr_sort___override(v___x_1502_);
return v_dummy_1503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(lean_object* v_motive_1504_, lean_object* v_fst_1505_, lean_object* v_snd_1506_, lean_object* v_minorArgs_1507_, lean_object* v_minorResultType_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_dummy_1514_; lean_object* v_nargs_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; 
v_dummy_1514_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_1515_ = l_Lean_Expr_getAppNumArgs(v_minorResultType_1508_);
lean_inc(v_nargs_1515_);
v___x_1516_ = lean_mk_array(v_nargs_1515_, v_dummy_1514_);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_sub(v_nargs_1515_, v___x_1517_);
lean_dec(v_nargs_1515_);
v___x_1519_ = lean_unbox(v_snd_1506_);
v___x_1520_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_1504_, v_fst_1505_, v___x_1519_, v_minorArgs_1507_, v_minorResultType_1508_, v___x_1516_, v___x_1518_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed(lean_object* v_motive_1521_, lean_object* v_fst_1522_, lean_object* v_snd_1523_, lean_object* v_minorArgs_1524_, lean_object* v_minorResultType_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(v_motive_1521_, v_fst_1522_, v_snd_1523_, v_minorArgs_1524_, v_minorResultType_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_minorArgs_1524_);
lean_dec(v_snd_1523_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(lean_object* v_upperBound_1532_, lean_object* v_motive_1533_, lean_object* v_xs_1534_, lean_object* v_numParams_1535_, lean_object* v_majorPos_1536_, lean_object* v_numIndices_1537_, lean_object* v_a_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_a_1546_; uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_lt(v_a_1538_, v_upperBound_1532_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_a_1538_);
lean_dec_ref(v_motive_1533_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_b_1539_);
return v___x_1551_;
}
else
{
lean_object* v_fst_1552_; lean_object* v_snd_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1584_; 
v_fst_1552_ = lean_ctor_get(v_b_1539_, 0);
v_snd_1553_ = lean_ctor_get(v_b_1539_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_b_1539_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1555_ = v_b_1539_;
v_isShared_1556_ = v_isSharedCheck_1584_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_snd_1553_);
lean_inc(v_fst_1552_);
lean_dec(v_b_1539_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1584_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v_recursor_1559_; 
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_numParams_1535_, v___x_1557_);
v_recursor_1559_ = lean_nat_dec_lt(v_a_1538_, v___x_1558_);
lean_dec(v___x_1558_);
if (v_recursor_1559_ == 0)
{
lean_object* v___f_1560_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
lean_inc(v_snd_1553_);
lean_inc(v_fst_1552_);
lean_inc_ref(v_motive_1533_);
v___f_1560_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1560_, 0, v_motive_1533_);
lean_closure_set(v___f_1560_, 1, v_fst_1552_);
lean_closure_set(v___f_1560_, 2, v_snd_1553_);
v___x_1575_ = lean_nat_sub(v_majorPos_1536_, v_numIndices_1537_);
v___x_1576_ = lean_nat_dec_le(v___x_1575_, v_a_1538_);
lean_dec(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_del_object(v___x_1555_);
lean_dec(v_snd_1553_);
lean_dec(v_fst_1552_);
goto v___jp_1561_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_le(v_a_1538_, v_majorPos_1536_);
if (v___x_1577_ == 0)
{
lean_del_object(v___x_1555_);
lean_dec(v_snd_1553_);
lean_dec(v_fst_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v___x_1579_; 
lean_dec_ref(v___f_1560_);
if (v_isShared_1556_ == 0)
{
v___x_1579_ = v___x_1555_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_fst_1552_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_snd_1553_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v_a_1546_ = v___x_1579_;
goto v___jp_1545_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_array_fget_borrowed(v_xs_1534_, v_a_1538_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___x_1562_);
v___x_1563_ = lean_infer_type(v___x_1562_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_1564_, v___f_1560_, v_recursor_1559_, v_recursor_1559_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v_a_1546_ = v_a_1566_;
goto v___jp_1545_;
}
else
{
lean_dec(v_a_1538_);
lean_dec_ref(v_motive_1533_);
return v___x_1565_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v___f_1560_);
lean_dec(v_a_1538_);
lean_dec_ref(v_motive_1533_);
v_a_1567_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1563_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1563_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
else
{
lean_object* v___x_1582_; 
if (v_isShared_1556_ == 0)
{
v___x_1582_ = v___x_1555_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_fst_1552_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_snd_1553_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
v_a_1546_ = v___x_1582_;
goto v___jp_1545_;
}
}
}
}
v___jp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_a_1538_, v___x_1547_);
lean_dec(v_a_1538_);
v_a_1538_ = v___x_1548_;
v_b_1539_ = v_a_1546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___boxed(lean_object* v_upperBound_1585_, lean_object* v_motive_1586_, lean_object* v_xs_1587_, lean_object* v_numParams_1588_, lean_object* v_majorPos_1589_, lean_object* v_numIndices_1590_, lean_object* v_a_1591_, lean_object* v_b_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1585_, v_motive_1586_, v_xs_1587_, v_numParams_1588_, v_majorPos_1589_, v_numIndices_1590_, v_a_1591_, v_b_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v_numIndices_1590_);
lean_dec(v_majorPos_1589_);
lean_dec(v_numParams_1588_);
lean_dec_ref(v_xs_1587_);
lean_dec(v_upperBound_1585_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(lean_object* v_xs_1605_, lean_object* v_numParams_1606_, lean_object* v_numIndices_1607_, lean_object* v_majorPos_1608_, lean_object* v_motive_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1615_ = lean_array_get_size(v_xs_1605_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1));
v___x_1618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v___x_1615_, v_motive_1609_, v_xs_1605_, v_numParams_1606_, v_majorPos_1608_, v_numIndices_1607_, v___x_1616_, v___x_1617_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1636_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1636_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1636_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_fst_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1635_; 
v_fst_1623_ = lean_ctor_get(v_a_1619_, 0);
v_snd_1624_ = lean_ctor_get(v_a_1619_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_a_1619_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1626_ = v_a_1619_;
v_isShared_1627_ = v_isSharedCheck_1635_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_inc(v_fst_1623_);
lean_dec(v_a_1619_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1635_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_array_to_list(v_fst_1623_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1628_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_snd_1624_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1630_);
v___x_1632_ = v___x_1621_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_a_1637_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1618_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1618_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(lean_object* v_xs_1645_, lean_object* v_numParams_1646_, lean_object* v_numIndices_1647_, lean_object* v_majorPos_1648_, lean_object* v_motive_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1645_, v_numParams_1646_, v_numIndices_1647_, v_majorPos_1648_, v_motive_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_majorPos_1648_);
lean_dec(v_numIndices_1647_);
lean_dec(v_numParams_1646_);
lean_dec_ref(v_xs_1645_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(lean_object* v_upperBound_1656_, lean_object* v_motive_1657_, lean_object* v_xs_1658_, lean_object* v_numParams_1659_, lean_object* v_majorPos_1660_, lean_object* v_numIndices_1661_, lean_object* v_inst_1662_, lean_object* v_R_1663_, lean_object* v_a_1664_, lean_object* v_b_1665_, lean_object* v_c_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_1656_, v_motive_1657_, v_xs_1658_, v_numParams_1659_, v_majorPos_1660_, v_numIndices_1661_, v_a_1664_, v_b_1665_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___boxed(lean_object* v_upperBound_1673_, lean_object* v_motive_1674_, lean_object* v_xs_1675_, lean_object* v_numParams_1676_, lean_object* v_majorPos_1677_, lean_object* v_numIndices_1678_, lean_object* v_inst_1679_, lean_object* v_R_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_, lean_object* v_c_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(v_upperBound_1673_, v_motive_1674_, v_xs_1675_, v_numParams_1676_, v_majorPos_1677_, v_numIndices_1678_, v_inst_1679_, v_R_1680_, v_a_1681_, v_b_1682_, v_c_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v_numIndices_1678_);
lean_dec(v_majorPos_1677_);
lean_dec(v_numParams_1676_);
lean_dec_ref(v_xs_1675_);
lean_dec(v_upperBound_1673_);
return v_res_1689_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(lean_object* v_declName_1693_, lean_object* v_motiveArgs_1694_, lean_object* v_motiveResultType_1695_, lean_object* v_motiveTypeParams_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
uint8_t v___y_1703_; uint8_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = l_Lean_Expr_isSort(v_motiveResultType_1695_);
v___x_1714_ = lean_bool_not(v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; uint8_t v___x_1718_; 
v___x_1715_ = lean_array_get_size(v_motiveArgs_1694_);
v___x_1716_ = lean_array_get_size(v_motiveTypeParams_1696_);
v___x_1717_ = lean_nat_dec_eq(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_bool_not(v___x_1717_);
v___y_1703_ = v___x_1718_;
goto v___jp_1702_;
}
else
{
v___y_1703_ = v___x_1714_;
goto v___jp_1702_;
}
v___jp_1702_:
{
if (v___y_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_declName_1693_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1707_ = 0;
v___x_1708_ = l_Lean_MessageData_ofConstName(v_declName_1693_, v___x_1707_);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1706_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1711_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(lean_object* v_declName_1719_, lean_object* v_motiveArgs_1720_, lean_object* v_motiveResultType_1721_, lean_object* v_motiveTypeParams_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1719_, v_motiveArgs_1720_, v_motiveResultType_1721_, v_motiveTypeParams_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec_ref(v_motiveTypeParams_1722_);
lean_dec_ref(v_motiveResultType_1721_);
lean_dec_ref(v_motiveArgs_1720_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(lean_object* v_declName_1729_, lean_object* v_motiveArgs_1730_, lean_object* v_a_1731_, lean_object* v_us_1732_, lean_object* v_xs_1733_, lean_object* v___x_1734_, lean_object* v___y_1735_, lean_object* v_fst_1736_, lean_object* v_motive_1737_, lean_object* v_declName_1738_, uint8_t v_snd_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_motiveTypeParams_1742_, lean_object* v_motiveResultType_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
lean_inc(v_declName_1729_);
v___x_1749_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(v_declName_1729_, v_motiveArgs_1730_, v_motiveResultType_1743_, v_motiveTypeParams_1742_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v___x_1750_; 
lean_dec_ref_known(v___x_1749_, 1);
lean_inc(v_declName_1729_);
v___x_1750_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(v_declName_1729_, v_motiveResultType_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_ConstantInfo_levelParams(v_a_1731_);
lean_inc(v_declName_1729_);
v___x_1753_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(v_declName_1729_, v___x_1752_, v_a_1751_, v_us_1732_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v_a_1751_);
lean_dec(v___x_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_1733_, v___x_1734_, v___y_1735_, v_fst_1736_, v_motive_1737_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1768_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1768_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1768_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1766_; 
v_fst_1760_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_fst_1760_);
v_snd_1761_ = lean_ctor_get(v_a_1756_, 1);
lean_inc(v_snd_1761_);
lean_dec(v_a_1756_);
v___x_1762_ = lean_array_get_size(v_xs_1733_);
v___x_1763_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1763_, 0, v_declName_1729_);
lean_ctor_set(v___x_1763_, 1, v_declName_1738_);
lean_ctor_set(v___x_1763_, 2, v_a_1754_);
lean_ctor_set(v___x_1763_, 3, v___x_1762_);
lean_ctor_set(v___x_1763_, 4, v_fst_1736_);
lean_ctor_set(v___x_1763_, 5, v_a_1740_);
lean_ctor_set(v___x_1763_, 6, v_a_1741_);
lean_ctor_set(v___x_1763_, 7, v_fst_1760_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*8, v_snd_1739_);
v___x_1764_ = lean_unbox(v_snd_1761_);
lean_dec(v_snd_1761_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*8 + 1, v___x_1764_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1763_);
v___x_1766_ = v___x_1758_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1763_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1754_);
lean_dec(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec(v_declName_1738_);
lean_dec(v_fst_1736_);
lean_dec(v_declName_1729_);
v_a_1769_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1755_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1755_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec(v_declName_1738_);
lean_dec_ref(v_motive_1737_);
lean_dec(v_fst_1736_);
lean_dec(v_declName_1729_);
v_a_1777_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1753_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1753_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec(v_declName_1738_);
lean_dec_ref(v_motive_1737_);
lean_dec(v_fst_1736_);
lean_dec(v_us_1732_);
lean_dec(v_declName_1729_);
v_a_1785_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1750_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1750_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec(v_declName_1738_);
lean_dec_ref(v_motive_1737_);
lean_dec(v_fst_1736_);
lean_dec(v_us_1732_);
lean_dec(v_declName_1729_);
v_a_1793_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1749_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1749_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed(lean_object** _args){
lean_object* v_declName_1801_ = _args[0];
lean_object* v_motiveArgs_1802_ = _args[1];
lean_object* v_a_1803_ = _args[2];
lean_object* v_us_1804_ = _args[3];
lean_object* v_xs_1805_ = _args[4];
lean_object* v___x_1806_ = _args[5];
lean_object* v___y_1807_ = _args[6];
lean_object* v_fst_1808_ = _args[7];
lean_object* v_motive_1809_ = _args[8];
lean_object* v_declName_1810_ = _args[9];
lean_object* v_snd_1811_ = _args[10];
lean_object* v_a_1812_ = _args[11];
lean_object* v_a_1813_ = _args[12];
lean_object* v_motiveTypeParams_1814_ = _args[13];
lean_object* v_motiveResultType_1815_ = _args[14];
lean_object* v___y_1816_ = _args[15];
lean_object* v___y_1817_ = _args[16];
lean_object* v___y_1818_ = _args[17];
lean_object* v___y_1819_ = _args[18];
lean_object* v___y_1820_ = _args[19];
_start:
{
uint8_t v_snd_5204__boxed_1821_; lean_object* v_res_1822_; 
v_snd_5204__boxed_1821_ = lean_unbox(v_snd_1811_);
v_res_1822_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(v_declName_1801_, v_motiveArgs_1802_, v_a_1803_, v_us_1804_, v_xs_1805_, v___x_1806_, v___y_1807_, v_fst_1808_, v_motive_1809_, v_declName_1810_, v_snd_5204__boxed_1821_, v_a_1812_, v_a_1813_, v_motiveTypeParams_1814_, v_motiveResultType_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_motiveResultType_1815_);
lean_dec_ref(v_motiveTypeParams_1814_);
lean_dec(v___y_1807_);
lean_dec(v___x_1806_);
lean_dec_ref(v_xs_1805_);
lean_dec_ref(v_a_1803_);
lean_dec_ref(v_motiveArgs_1802_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(lean_object* v_declName_1826_, lean_object* v_xs_1827_, lean_object* v___x_1828_, lean_object* v_fst_1829_, lean_object* v___y_1830_, lean_object* v_motiveArgs_1831_, lean_object* v_a_1832_, lean_object* v_motive_1833_, uint8_t v_snd_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
if (lean_obj_tag(v_x_1835_) == 5)
{
lean_object* v_fn_1843_; lean_object* v_arg_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_fn_1843_ = lean_ctor_get(v_x_1835_, 0);
lean_inc_ref(v_fn_1843_);
v_arg_1844_ = lean_ctor_get(v_x_1835_, 1);
lean_inc_ref(v_arg_1844_);
lean_dec_ref_known(v_x_1835_, 2);
v___x_1845_ = lean_array_set(v_x_1836_, v_x_1837_, v_arg_1844_);
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_nat_sub(v_x_1837_, v___x_1846_);
lean_dec(v_x_1837_);
v_x_1835_ = v_fn_1843_;
v_x_1836_ = v___x_1845_;
v_x_1837_ = v___x_1847_;
goto _start;
}
else
{
lean_dec(v_x_1837_);
if (lean_obj_tag(v_x_1835_) == 4)
{
lean_object* v_declName_1849_; lean_object* v_us_1850_; lean_object* v___x_1851_; 
v_declName_1849_ = lean_ctor_get(v_x_1835_, 0);
lean_inc(v_declName_1849_);
v_us_1850_ = lean_ctor_get(v_x_1835_, 1);
lean_inc(v_us_1850_);
lean_dec_ref_known(v_x_1835_, 2);
lean_inc(v_declName_1826_);
v___x_1851_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(v_declName_1826_, v_xs_1827_, v___x_1828_, v_x_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
lean_inc(v_declName_1826_);
v___x_1853_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(v_declName_1826_, v_xs_1827_, v_fst_1829_, v___y_1830_, v_x_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec_ref(v_x_1836_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
lean_inc_ref(v_motive_1833_);
v___x_1855_ = lean_infer_type(v_motive_1833_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v___f_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = lean_box(v_snd_1834_);
v___f_1858_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed), 20, 13);
lean_closure_set(v___f_1858_, 0, v_declName_1826_);
lean_closure_set(v___f_1858_, 1, v_motiveArgs_1831_);
lean_closure_set(v___f_1858_, 2, v_a_1832_);
lean_closure_set(v___f_1858_, 3, v_us_1850_);
lean_closure_set(v___f_1858_, 4, v_xs_1827_);
lean_closure_set(v___f_1858_, 5, v___x_1828_);
lean_closure_set(v___f_1858_, 6, v___y_1830_);
lean_closure_set(v___f_1858_, 7, v_fst_1829_);
lean_closure_set(v___f_1858_, 8, v_motive_1833_);
lean_closure_set(v___f_1858_, 9, v_declName_1849_);
lean_closure_set(v___f_1858_, 10, v___x_1857_);
lean_closure_set(v___f_1858_, 11, v_a_1852_);
lean_closure_set(v___f_1858_, 12, v_a_1854_);
v___x_1859_ = 0;
v___x_1860_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_1856_, v___f_1858_, v___x_1859_, v___x_1859_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1860_;
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1854_);
lean_dec(v_a_1852_);
lean_dec(v_us_1850_);
lean_dec(v_declName_1849_);
lean_dec_ref(v_motive_1833_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_motiveArgs_1831_);
lean_dec(v___y_1830_);
lean_dec(v_fst_1829_);
lean_dec(v___x_1828_);
lean_dec_ref(v_xs_1827_);
lean_dec(v_declName_1826_);
v_a_1861_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1855_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1855_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1852_);
lean_dec(v_us_1850_);
lean_dec(v_declName_1849_);
lean_dec_ref(v_motive_1833_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_motiveArgs_1831_);
lean_dec(v___y_1830_);
lean_dec(v_fst_1829_);
lean_dec(v___x_1828_);
lean_dec_ref(v_xs_1827_);
lean_dec(v_declName_1826_);
v_a_1869_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1853_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1853_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_us_1850_);
lean_dec(v_declName_1849_);
lean_dec_ref(v_x_1836_);
lean_dec_ref(v_motive_1833_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_motiveArgs_1831_);
lean_dec(v___y_1830_);
lean_dec(v_fst_1829_);
lean_dec(v___x_1828_);
lean_dec_ref(v_xs_1827_);
lean_dec(v_declName_1826_);
v_a_1877_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1851_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1851_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v_x_1836_);
lean_dec_ref(v_x_1835_);
lean_dec_ref(v_motive_1833_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_motiveArgs_1831_);
lean_dec(v___y_1830_);
lean_dec(v_fst_1829_);
lean_dec(v___x_1828_);
lean_dec_ref(v_xs_1827_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1886_ = 0;
v___x_1887_ = l_Lean_MessageData_ofConstName(v_declName_1826_, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1885_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1890_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___boxed(lean_object** _args){
lean_object* v_declName_1892_ = _args[0];
lean_object* v_xs_1893_ = _args[1];
lean_object* v___x_1894_ = _args[2];
lean_object* v_fst_1895_ = _args[3];
lean_object* v___y_1896_ = _args[4];
lean_object* v_motiveArgs_1897_ = _args[5];
lean_object* v_a_1898_ = _args[6];
lean_object* v_motive_1899_ = _args[7];
lean_object* v_snd_1900_ = _args[8];
lean_object* v_x_1901_ = _args[9];
lean_object* v_x_1902_ = _args[10];
lean_object* v_x_1903_ = _args[11];
lean_object* v___y_1904_ = _args[12];
lean_object* v___y_1905_ = _args[13];
lean_object* v___y_1906_ = _args[14];
lean_object* v___y_1907_ = _args[15];
lean_object* v___y_1908_ = _args[16];
_start:
{
uint8_t v_snd_5358__boxed_1909_; lean_object* v_res_1910_; 
v_snd_5358__boxed_1909_ = lean_unbox(v_snd_1900_);
v_res_1910_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1892_, v_xs_1893_, v___x_1894_, v_fst_1895_, v___y_1896_, v_motiveArgs_1897_, v_a_1898_, v_motive_1899_, v_snd_5358__boxed_1909_, v_x_1901_, v_x_1902_, v_x_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0));
v___x_1913_ = l_Lean_stringToMessageData(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(lean_object* v_declName_1914_, lean_object* v_a_1915_, lean_object* v_xs_1916_, lean_object* v_a_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
if (lean_obj_tag(v_x_1918_) == 5)
{
lean_object* v_fn_1926_; lean_object* v_arg_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_fn_1926_ = lean_ctor_get(v_x_1918_, 0);
lean_inc_ref(v_fn_1926_);
v_arg_1927_ = lean_ctor_get(v_x_1918_, 1);
lean_inc_ref(v_arg_1927_);
lean_dec_ref_known(v_x_1918_, 2);
v___x_1928_ = lean_array_set(v_x_1919_, v_x_1920_, v_arg_1927_);
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_nat_sub(v_x_1920_, v___x_1929_);
lean_dec(v_x_1920_);
v_x_1918_ = v_fn_1926_;
v_x_1919_ = v___x_1928_;
v_x_1920_ = v___x_1930_;
goto _start;
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_x_1920_);
lean_inc(v_declName_1914_);
v___x_1932_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(v_declName_1914_, v_x_1918_, v_x_1919_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref_known(v___x_1932_, 1);
lean_inc(v_declName_1914_);
v___x_1933_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(v_declName_1914_, v_a_1915_, v_xs_1916_, v_x_1919_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v_snd_1935_; lean_object* v_fst_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1998_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v_snd_1935_ = lean_ctor_get(v_a_1934_, 1);
v_fst_1936_ = lean_ctor_get(v_a_1934_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_a_1934_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1938_ = v_a_1934_;
v_isShared_1939_ = v_isSharedCheck_1998_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_snd_1935_);
lean_inc(v_fst_1936_);
lean_dec(v_a_1934_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1998_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1997_; 
v_fst_1940_ = lean_ctor_get(v_snd_1935_, 0);
v_snd_1941_ = lean_ctor_get(v_snd_1935_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_snd_1935_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1943_ = v_snd_1935_;
v_isShared_1944_ = v_isSharedCheck_1997_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_snd_1941_);
lean_inc(v_fst_1940_);
lean_dec(v_snd_1935_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1997_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1971_; uint8_t v___x_1992_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(v_xs_1916_, v_x_1918_, v___x_1945_);
v___x_1992_ = lean_unbox(v_snd_1941_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_array_get_size(v_x_1919_);
v___y_1971_ = v___x_1993_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_array_get_size(v_x_1919_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_sub(v___x_1994_, v___x_1995_);
v___y_1971_ = v___x_1996_;
goto v___jp_1970_;
}
v___jp_1947_:
{
lean_object* v___x_1953_; 
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
v___x_1953_ = lean_infer_type(v_fst_1936_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_dummy_1955_; lean_object* v_nargs_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v_dummy_1955_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_1956_ = l_Lean_Expr_getAppNumArgs(v_a_1954_);
lean_inc(v_nargs_1956_);
v___x_1957_ = lean_mk_array(v_nargs_1956_, v_dummy_1955_);
v___x_1958_ = lean_unsigned_to_nat(1u);
v___x_1959_ = lean_nat_sub(v_nargs_1956_, v___x_1958_);
lean_dec(v_nargs_1956_);
v___x_1960_ = lean_unbox(v_snd_1941_);
lean_dec(v_snd_1941_);
v___x_1961_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_1914_, v_xs_1916_, v___x_1946_, v_fst_1940_, v___y_1948_, v_x_1919_, v_a_1917_, v_x_1918_, v___x_1960_, v_a_1954_, v___x_1957_, v___x_1959_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v___x_1961_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___y_1948_);
lean_dec(v___x_1946_);
lean_dec(v_snd_1941_);
lean_dec(v_fst_1940_);
lean_dec_ref(v_x_1919_);
lean_dec_ref(v_x_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_xs_1916_);
lean_dec(v_declName_1914_);
v_a_1962_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1953_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1953_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
v___jp_1970_:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_nat_dec_lt(v_fst_1940_, v___y_1971_);
if (v___x_1972_ == 0)
{
lean_del_object(v___x_1943_);
lean_del_object(v___x_1938_);
v___y_1948_ = v___y_1971_;
v___y_1949_ = v___y_1921_;
v___y_1950_ = v___y_1922_;
v___y_1951_ = v___y_1923_;
v___y_1952_ = v___y_1924_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec(v___y_1971_);
lean_dec(v___x_1946_);
lean_dec(v_snd_1941_);
lean_dec(v_fst_1940_);
lean_dec(v_fst_1936_);
lean_dec_ref(v_x_1919_);
lean_dec_ref(v_x_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_xs_1916_);
v___x_1973_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
v___x_1974_ = 0;
v___x_1975_ = l_Lean_MessageData_ofConstName(v_declName_1914_, v___x_1974_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 7);
lean_ctor_set(v___x_1943_, 1, v___x_1975_);
lean_ctor_set(v___x_1943_, 0, v___x_1973_);
v___x_1977_ = v___x_1943_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1);
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 7);
lean_ctor_set(v___x_1938_, 1, v___x_1978_);
lean_ctor_set(v___x_1938_, 0, v___x_1977_);
v___x_1980_ = v___x_1938_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v___x_1981_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_1980_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
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
}
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_x_1919_);
lean_dec_ref(v_x_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_xs_1916_);
lean_dec(v_declName_1914_);
v_a_1999_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1933_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1933_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v_x_1919_);
lean_dec_ref(v_x_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_xs_1916_);
lean_dec(v_a_1915_);
lean_dec(v_declName_1914_);
v_a_2007_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1932_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1932_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___boxed(lean_object* v_declName_2015_, lean_object* v_a_2016_, lean_object* v_xs_2017_, lean_object* v_a_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_2015_, v_a_2016_, v_xs_2017_, v_a_2018_, v_x_2019_, v_x_2020_, v_x_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(lean_object* v_declName_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_xs_2031_, lean_object* v_type_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_dummy_2038_; lean_object* v_nargs_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_dummy_2038_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
v_nargs_2039_ = l_Lean_Expr_getAppNumArgs(v_type_2032_);
lean_inc(v_nargs_2039_);
v___x_2040_ = lean_mk_array(v_nargs_2039_, v_dummy_2038_);
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_sub(v_nargs_2039_, v___x_2041_);
lean_dec(v_nargs_2039_);
v___x_2043_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_2028_, v_a_2029_, v_xs_2031_, v_a_2030_, v_type_2032_, v___x_2040_, v___x_2042_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed(lean_object* v_declName_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_xs_2047_, lean_object* v_type_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(v_declName_2044_, v_a_2045_, v_a_2046_, v_xs_2047_, v_type_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_2055_, lean_object* v_msg_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_fileName_2062_; lean_object* v_fileMap_2063_; lean_object* v_options_2064_; lean_object* v_currRecDepth_2065_; lean_object* v_maxRecDepth_2066_; lean_object* v_ref_2067_; lean_object* v_currNamespace_2068_; lean_object* v_openDecls_2069_; lean_object* v_initHeartbeats_2070_; lean_object* v_maxHeartbeats_2071_; lean_object* v_quotContext_2072_; lean_object* v_currMacroScope_2073_; uint8_t v_diag_2074_; lean_object* v_cancelTk_x3f_2075_; uint8_t v_suppressElabErrors_2076_; lean_object* v_inheritedTraceOptions_2077_; lean_object* v_ref_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_fileName_2062_ = lean_ctor_get(v___y_2059_, 0);
v_fileMap_2063_ = lean_ctor_get(v___y_2059_, 1);
v_options_2064_ = lean_ctor_get(v___y_2059_, 2);
v_currRecDepth_2065_ = lean_ctor_get(v___y_2059_, 3);
v_maxRecDepth_2066_ = lean_ctor_get(v___y_2059_, 4);
v_ref_2067_ = lean_ctor_get(v___y_2059_, 5);
v_currNamespace_2068_ = lean_ctor_get(v___y_2059_, 6);
v_openDecls_2069_ = lean_ctor_get(v___y_2059_, 7);
v_initHeartbeats_2070_ = lean_ctor_get(v___y_2059_, 8);
v_maxHeartbeats_2071_ = lean_ctor_get(v___y_2059_, 9);
v_quotContext_2072_ = lean_ctor_get(v___y_2059_, 10);
v_currMacroScope_2073_ = lean_ctor_get(v___y_2059_, 11);
v_diag_2074_ = lean_ctor_get_uint8(v___y_2059_, sizeof(void*)*14);
v_cancelTk_x3f_2075_ = lean_ctor_get(v___y_2059_, 12);
v_suppressElabErrors_2076_ = lean_ctor_get_uint8(v___y_2059_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2077_ = lean_ctor_get(v___y_2059_, 13);
v_ref_2078_ = l_Lean_replaceRef(v_ref_2055_, v_ref_2067_);
lean_inc_ref(v_inheritedTraceOptions_2077_);
lean_inc(v_cancelTk_x3f_2075_);
lean_inc(v_currMacroScope_2073_);
lean_inc(v_quotContext_2072_);
lean_inc(v_maxHeartbeats_2071_);
lean_inc(v_initHeartbeats_2070_);
lean_inc(v_openDecls_2069_);
lean_inc(v_currNamespace_2068_);
lean_inc(v_maxRecDepth_2066_);
lean_inc(v_currRecDepth_2065_);
lean_inc_ref(v_options_2064_);
lean_inc_ref(v_fileMap_2063_);
lean_inc_ref(v_fileName_2062_);
v___x_2079_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2079_, 0, v_fileName_2062_);
lean_ctor_set(v___x_2079_, 1, v_fileMap_2063_);
lean_ctor_set(v___x_2079_, 2, v_options_2064_);
lean_ctor_set(v___x_2079_, 3, v_currRecDepth_2065_);
lean_ctor_set(v___x_2079_, 4, v_maxRecDepth_2066_);
lean_ctor_set(v___x_2079_, 5, v_ref_2078_);
lean_ctor_set(v___x_2079_, 6, v_currNamespace_2068_);
lean_ctor_set(v___x_2079_, 7, v_openDecls_2069_);
lean_ctor_set(v___x_2079_, 8, v_initHeartbeats_2070_);
lean_ctor_set(v___x_2079_, 9, v_maxHeartbeats_2071_);
lean_ctor_set(v___x_2079_, 10, v_quotContext_2072_);
lean_ctor_set(v___x_2079_, 11, v_currMacroScope_2073_);
lean_ctor_set(v___x_2079_, 12, v_cancelTk_x3f_2075_);
lean_ctor_set(v___x_2079_, 13, v_inheritedTraceOptions_2077_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*14, v_diag_2074_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*14 + 1, v_suppressElabErrors_2076_);
v___x_2080_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_2056_, v___y_2057_, v___y_2058_, v___x_2079_, v___y_2060_);
lean_dec_ref_known(v___x_2079_, 14);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_2081_, lean_object* v_msg_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2081_, v_msg_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v_ref_2081_);
return v_res_2088_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
lean_ctor_set(v___x_2094_, 3, v___x_2093_);
lean_ctor_set(v___x_2094_, 4, v___x_2092_);
lean_ctor_set(v___x_2094_, 5, v___x_2092_);
lean_ctor_set(v___x_2094_, 6, v___x_2092_);
lean_ctor_set(v___x_2094_, 7, v___x_2092_);
lean_ctor_set(v___x_2094_, 8, v___x_2092_);
lean_ctor_set(v___x_2094_, 9, v___x_2092_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(32u);
v___x_2096_ = lean_mk_empty_array_with_capacity(v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2098_ = ((size_t)5ULL);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = lean_unsigned_to_nat(32u);
v___x_2101_ = lean_mk_empty_array_with_capacity(v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_2103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2099_);
lean_ctor_set(v___x_2103_, 3, v___x_2099_);
lean_ctor_set_usize(v___x_2103_, 4, v___x_2098_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2104_ = lean_box(1);
v___x_2105_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2105_);
lean_ctor_set(v___x_2107_, 2, v___x_2104_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_2128_ = l_Lean_stringToMessageData(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_2129_, lean_object* v_declHint_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v_env_2134_; uint8_t v___y_2136_; uint8_t v___x_2192_; uint8_t v___x_2193_; 
v___x_2133_ = lean_st_ref_get(v___y_2131_);
v_env_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_ref(v_env_2134_);
lean_dec(v___x_2133_);
v___x_2192_ = l_Lean_Name_isAnonymous(v_declHint_2130_);
v___x_2193_ = lean_bool_not(v___x_2192_);
if (v___x_2193_ == 0)
{
v___y_2136_ = v___x_2193_;
goto v___jp_2135_;
}
else
{
uint8_t v_isExporting_2194_; 
v_isExporting_2194_ = lean_ctor_get_uint8(v_env_2134_, sizeof(void*)*8);
v___y_2136_ = v_isExporting_2194_;
goto v___jp_2135_;
}
v___jp_2135_:
{
if (v___y_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref(v_env_2134_);
lean_dec(v_declHint_2130_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v_msg_2129_);
return v___x_2137_;
}
else
{
uint8_t v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = 0;
lean_inc_ref(v_env_2134_);
v___x_2139_ = l_Lean_Environment_setExporting(v_env_2134_, v___x_2138_);
lean_inc(v_declHint_2130_);
lean_inc_ref(v___x_2139_);
v___x_2140_ = l_Lean_Environment_contains(v___x_2139_, v_declHint_2130_, v___y_2136_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec_ref(v___x_2139_);
lean_dec_ref(v_env_2134_);
lean_dec(v_declHint_2130_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_msg_2129_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_c_2147_; lean_object* v___x_2148_; 
v___x_2142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_2144_ = l_Lean_Options_empty;
v___x_2145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2139_);
lean_ctor_set(v___x_2145_, 1, v___x_2142_);
lean_ctor_set(v___x_2145_, 2, v___x_2143_);
lean_ctor_set(v___x_2145_, 3, v___x_2144_);
lean_inc(v_declHint_2130_);
v___x_2146_ = l_Lean_MessageData_ofConstName(v_declHint_2130_, v___x_2138_);
v_c_2147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2147_, 0, v___x_2145_);
lean_ctor_set(v_c_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2134_, v_declHint_2130_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v_env_2134_);
lean_dec(v_declHint_2130_);
v___x_2149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v_c_2147_);
v___x_2151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_MessageData_note(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_msg_2129_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
else
{
lean_object* v_val_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2191_; 
v_val_2156_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2158_ = v___x_2148_;
v_isShared_2159_ = v_isSharedCheck_2191_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_val_2156_);
lean_dec(v___x_2148_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2191_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_mod_2163_; uint8_t v___x_2164_; 
v___x_2160_ = lean_box(0);
v___x_2161_ = l_Lean_Environment_header(v_env_2134_);
lean_dec_ref(v_env_2134_);
v___x_2162_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2161_);
v_mod_2163_ = lean_array_get(v___x_2160_, v___x_2162_, v_val_2156_);
lean_dec(v_val_2156_);
lean_dec_ref(v___x_2162_);
v___x_2164_ = l_Lean_isPrivateName(v_declHint_2130_);
lean_dec(v_declHint_2130_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v_c_2147_);
v___x_2167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_MessageData_ofName(v_mod_2163_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_MessageData_note(v___x_2172_);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_msg_2129_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2174_);
v___x_2176_ = v___x_2158_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v_c_2147_);
v___x_2180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = l_Lean_MessageData_ofName(v_mod_2163_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_MessageData_note(v___x_2185_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_msg_2129_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2187_);
v___x_2189_ = v___x_2158_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2195_, lean_object* v_declHint_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2195_, v_declHint_2196_, v___y_2197_);
lean_dec(v___y_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_2200_, lean_object* v_declHint_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2217_; 
v___x_2207_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2200_, v_declHint_2201_, v___y_2205_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2217_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2217_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2212_ = l_Lean_unknownIdentifierMessageTag;
v___x_2213_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v_a_2208_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2213_);
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_2218_, lean_object* v_declHint_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2218_, v_declHint_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2226_, lean_object* v_msg_2227_, lean_object* v_declHint_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v_a_2235_; lean_object* v___x_2236_; 
v___x_2234_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2227_, v_declHint_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2226_, v_a_2235_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2237_, lean_object* v_msg_2238_, lean_object* v_declHint_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2237_, v_msg_2238_, v_declHint_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v_ref_2237_);
return v_res_2245_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2249_, lean_object* v_constName_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2256_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2257_ = 0;
lean_inc(v_constName_2250_);
v___x_2258_ = l_Lean_MessageData_ofConstName(v_constName_2250_, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1, &l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once, _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2249_, v___x_2261_, v_constName_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2263_, lean_object* v_constName_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2263_, v_constName_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_ref_2263_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(lean_object* v_constName_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_ref_2277_; lean_object* v___x_2278_; 
v_ref_2277_ = lean_ctor_get(v___y_2274_, 5);
v___x_2278_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2277_, v_constName_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; lean_object* v_env_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2292_ = lean_st_ref_get(v___y_2290_);
v_env_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_ref(v_env_2293_);
lean_dec(v___x_2292_);
v___x_2294_ = 0;
lean_inc(v_constName_2286_);
v___x_2295_ = l_Lean_Environment_find_x3f(v_env_2293_, v_constName_2286_, v___x_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2296_;
}
else
{
lean_object* v_val_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_constName_2286_);
v_val_2297_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2295_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_val_2297_);
lean_dec(v___x_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 0);
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_val_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0___boxed(lean_object* v_constName_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_constName_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(lean_object* v_declName_2312_, lean_object* v_majorPos_x3f_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
lean_inc(v_declName_2312_);
v___x_2319_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_declName_2312_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
lean_inc(v_declName_2312_);
v___x_2321_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_2312_, v_majorPos_x3f_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
lean_inc(v_a_2320_);
v___f_2323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2323_, 0, v_declName_2312_);
lean_closure_set(v___f_2323_, 1, v_a_2322_);
lean_closure_set(v___f_2323_, 2, v_a_2320_);
v___x_2324_ = l_Lean_ConstantInfo_type(v_a_2320_);
lean_dec(v_a_2320_);
v___x_2325_ = 0;
v___x_2326_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v___x_2324_, v___f_2323_, v___x_2325_, v___x_2325_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
return v___x_2326_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_a_2320_);
lean_dec(v_declName_2312_);
v_a_2327_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2321_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2321_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_majorPos_x3f_2313_);
lean_dec(v_declName_2312_);
v_a_2335_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2319_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2319_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___boxed(lean_object* v_declName_2343_, lean_object* v_majorPos_x3f_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2343_, v_majorPos_x3f_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(lean_object* v_00_u03b1_2351_, lean_object* v_constName_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2359_, lean_object* v_constName_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(v_00_u03b1_2359_, v_constName_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2367_, lean_object* v_ref_2368_, lean_object* v_constName_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_2368_, v_constName_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_ref_2377_, lean_object* v_constName_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(v_00_u03b1_2376_, v_ref_2377_, v_constName_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_ref_2377_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2385_, lean_object* v_ref_2386_, lean_object* v_msg_2387_, lean_object* v_declHint_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2386_, v_msg_2387_, v_declHint_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_ref_2396_, lean_object* v_msg_2397_, lean_object* v_declHint_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2395_, v_ref_2396_, v_msg_2397_, v_declHint_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_ref_2396_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_2405_, lean_object* v_declHint_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2405_, v_declHint_2406_, v___y_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2413_, lean_object* v_declHint_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2413_, v_declHint_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2421_, lean_object* v_ref_2422_, lean_object* v_msg_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2422_, v_msg_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2430_, lean_object* v_ref_2431_, lean_object* v_msg_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2430_, v_ref_2431_, v_msg_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v_ref_2431_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(lean_object* v_msgData_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v_env_2444_; lean_object* v_options_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2443_ = lean_st_ref_get(v___y_2441_);
v_env_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc_ref(v_env_2444_);
lean_dec(v___x_2443_);
v_options_2445_ = lean_ctor_get(v___y_2440_, 2);
v___x_2446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_2447_ = lean_unsigned_to_nat(32u);
v___x_2448_ = lean_mk_empty_array_with_capacity(v___x_2447_);
lean_dec_ref(v___x_2448_);
v___x_2449_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2445_);
v___x_2450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2450_, 0, v_env_2444_);
lean_ctor_set(v___x_2450_, 1, v___x_2446_);
lean_ctor_set(v___x_2450_, 2, v___x_2449_);
lean_ctor_set(v___x_2450_, 3, v_options_2445_);
v___x_2451_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
lean_ctor_set(v___x_2451_, 1, v_msgData_2439_);
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msgData_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(lean_object* v_msg_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_ref_2462_; lean_object* v___x_2463_; lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2472_; 
v_ref_2462_ = lean_ctor_get(v___y_2459_, 5);
v___x_2463_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msg_2458_, v___y_2459_, v___y_2460_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_inc(v_ref_2462_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_ref_2462_);
lean_ctor_set(v___x_2468_, 1, v_a_2464_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set_tag(v___x_2466_, 1);
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(lean_object* v_ref_2478_, lean_object* v_msg_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_fileName_2483_; lean_object* v_fileMap_2484_; lean_object* v_options_2485_; lean_object* v_currRecDepth_2486_; lean_object* v_maxRecDepth_2487_; lean_object* v_ref_2488_; lean_object* v_currNamespace_2489_; lean_object* v_openDecls_2490_; lean_object* v_initHeartbeats_2491_; lean_object* v_maxHeartbeats_2492_; lean_object* v_quotContext_2493_; lean_object* v_currMacroScope_2494_; uint8_t v_diag_2495_; lean_object* v_cancelTk_x3f_2496_; uint8_t v_suppressElabErrors_2497_; lean_object* v_inheritedTraceOptions_2498_; lean_object* v_ref_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_fileName_2483_ = lean_ctor_get(v___y_2480_, 0);
v_fileMap_2484_ = lean_ctor_get(v___y_2480_, 1);
v_options_2485_ = lean_ctor_get(v___y_2480_, 2);
v_currRecDepth_2486_ = lean_ctor_get(v___y_2480_, 3);
v_maxRecDepth_2487_ = lean_ctor_get(v___y_2480_, 4);
v_ref_2488_ = lean_ctor_get(v___y_2480_, 5);
v_currNamespace_2489_ = lean_ctor_get(v___y_2480_, 6);
v_openDecls_2490_ = lean_ctor_get(v___y_2480_, 7);
v_initHeartbeats_2491_ = lean_ctor_get(v___y_2480_, 8);
v_maxHeartbeats_2492_ = lean_ctor_get(v___y_2480_, 9);
v_quotContext_2493_ = lean_ctor_get(v___y_2480_, 10);
v_currMacroScope_2494_ = lean_ctor_get(v___y_2480_, 11);
v_diag_2495_ = lean_ctor_get_uint8(v___y_2480_, sizeof(void*)*14);
v_cancelTk_x3f_2496_ = lean_ctor_get(v___y_2480_, 12);
v_suppressElabErrors_2497_ = lean_ctor_get_uint8(v___y_2480_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2498_ = lean_ctor_get(v___y_2480_, 13);
v_ref_2499_ = l_Lean_replaceRef(v_ref_2478_, v_ref_2488_);
lean_inc_ref(v_inheritedTraceOptions_2498_);
lean_inc(v_cancelTk_x3f_2496_);
lean_inc(v_currMacroScope_2494_);
lean_inc(v_quotContext_2493_);
lean_inc(v_maxHeartbeats_2492_);
lean_inc(v_initHeartbeats_2491_);
lean_inc(v_openDecls_2490_);
lean_inc(v_currNamespace_2489_);
lean_inc(v_maxRecDepth_2487_);
lean_inc(v_currRecDepth_2486_);
lean_inc_ref(v_options_2485_);
lean_inc_ref(v_fileMap_2484_);
lean_inc_ref(v_fileName_2483_);
v___x_2500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2500_, 0, v_fileName_2483_);
lean_ctor_set(v___x_2500_, 1, v_fileMap_2484_);
lean_ctor_set(v___x_2500_, 2, v_options_2485_);
lean_ctor_set(v___x_2500_, 3, v_currRecDepth_2486_);
lean_ctor_set(v___x_2500_, 4, v_maxRecDepth_2487_);
lean_ctor_set(v___x_2500_, 5, v_ref_2499_);
lean_ctor_set(v___x_2500_, 6, v_currNamespace_2489_);
lean_ctor_set(v___x_2500_, 7, v_openDecls_2490_);
lean_ctor_set(v___x_2500_, 8, v_initHeartbeats_2491_);
lean_ctor_set(v___x_2500_, 9, v_maxHeartbeats_2492_);
lean_ctor_set(v___x_2500_, 10, v_quotContext_2493_);
lean_ctor_set(v___x_2500_, 11, v_currMacroScope_2494_);
lean_ctor_set(v___x_2500_, 12, v_cancelTk_x3f_2496_);
lean_ctor_set(v___x_2500_, 13, v_inheritedTraceOptions_2498_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*14, v_diag_2495_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*14 + 1, v_suppressElabErrors_2497_);
v___x_2501_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2479_, v___x_2500_, v___y_2481_);
lean_dec_ref_known(v___x_2500_, 14);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg___boxed(lean_object* v_ref_2502_, lean_object* v_msg_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2502_, v_msg_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v_ref_2502_);
return v_res_2507_;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos(lean_object* v_stx_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
lean_inc(v_stx_2523_);
v___x_2527_ = l_Lean_Syntax_getKind(v_stx_2523_);
v___x_2528_ = ((lean_object*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4));
v___x_2529_ = lean_name_eq(v___x_2527_, v___x_2528_);
lean_dec(v___x_2527_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_obj_once(&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6, &l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6_once, _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6);
v___x_2531_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_2523_, v___x_2530_, v_a_2524_, v_a_2525_);
lean_dec(v_stx_2523_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v___y_2534_; lean_object* v___y_2538_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2551_ = l_Lean_Syntax_getArg(v_stx_2523_, v___x_2532_);
v___x_2552_ = l_Lean_Syntax_isNatLit_x3f(v___x_2551_);
lean_dec(v___x_2551_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_unsigned_to_nat(0u);
v___y_2538_ = v___x_2553_;
goto v___jp_2537_;
}
else
{
lean_object* v_val_2554_; 
v_val_2554_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v___x_2552_, 1);
v___y_2538_ = v_val_2554_;
goto v___jp_2537_;
}
v___jp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_nat_sub(v___y_2534_, v___x_2532_);
lean_dec(v___y_2534_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
v___jp_2537_:
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_unsigned_to_nat(0u);
v___x_2540_ = lean_nat_dec_eq(v___y_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_dec(v_stx_2523_);
v___y_2534_ = v___y_2538_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v___y_2538_);
v___x_2541_ = lean_obj_once(&l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8, &l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8_once, _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8);
v___x_2542_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_2523_, v___x_2541_, v_a_2524_, v_a_2525_);
lean_dec(v_stx_2523_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
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
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(lean_object* v_stx_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(lean_object* v_00_u03b1_2560_, lean_object* v_ref_2561_, lean_object* v_msg_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_ref_2561_, v_msg_2562_, v___y_2563_, v___y_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_ref_2568_, lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(v_00_u03b1_2567_, v_ref_2568_, v_msg_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v_ref_2568_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(lean_object* v_00_u03b1_2574_, lean_object* v_msg_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_msg_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(v_00_u03b1_2580_, v_msg_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v_x_2586_, lean_object* v_stx_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_x_2592_, lean_object* v_stx_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_x_2592_, v_stx_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v_x_2592_);
return v_res_2597_;
}
}
static uint64_t _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2604_; uint64_t v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2605_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_uint64_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2608_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set_uint64(v___x_2608_, sizeof(void*)*1, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2609_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2612_ = lean_box(1);
v___x_2613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2613_);
lean_ctor_set(v___x_2615_, 2, v___x_2612_);
return v___x_2615_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
lean_ctor_set(v___x_2620_, 2, v___x_2619_);
lean_ctor_set(v___x_2620_, 3, v___x_2619_);
lean_ctor_set(v___x_2620_, 4, v___x_2618_);
lean_ctor_set(v___x_2620_, 5, v___x_2618_);
lean_ctor_set(v___x_2620_, 6, v___x_2618_);
lean_ctor_set(v___x_2620_, 7, v___x_2618_);
lean_ctor_set(v___x_2620_, 8, v___x_2618_);
lean_ctor_set(v___x_2620_, 9, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2622_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
lean_ctor_set(v___x_2622_, 2, v___x_2621_);
lean_ctor_set(v___x_2622_, 3, v___x_2621_);
lean_ctor_set(v___x_2622_, 4, v___x_2621_);
lean_ctor_set(v___x_2622_, 5, v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_ctor_set(v___x_2624_, 2, v___x_2623_);
lean_ctor_set(v___x_2624_, 3, v___x_2623_);
lean_ctor_set(v___x_2624_, 4, v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(lean_object* v___x_2625_, lean_object* v_declName_2626_, lean_object* v_majorPos_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2631_ = 0;
v___x_2632_ = 1;
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2637_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2638_ = lean_box(0);
lean_inc(v___x_2625_);
v___x_2639_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2639_, 0, v___x_2633_);
lean_ctor_set(v___x_2639_, 1, v___x_2625_);
lean_ctor_set(v___x_2639_, 2, v___x_2636_);
lean_ctor_set(v___x_2639_, 3, v___x_2637_);
lean_ctor_set(v___x_2639_, 4, v___x_2638_);
lean_ctor_set(v___x_2639_, 5, v___x_2634_);
lean_ctor_set(v___x_2639_, 6, v___x_2638_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7, v___x_2631_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7 + 1, v___x_2631_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7 + 2, v___x_2631_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*7 + 3, v___x_2632_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2641_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2642_ = lean_obj_once(&l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_, &l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
v___x_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2640_);
lean_ctor_set(v___x_2643_, 1, v___x_2641_);
lean_ctor_set(v___x_2643_, 2, v___x_2625_);
lean_ctor_set(v___x_2643_, 3, v___x_2635_);
lean_ctor_set(v___x_2643_, 4, v___x_2642_);
v___x_2644_ = lean_st_mk_ref(v___x_2643_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_majorPos_2627_);
v___x_2646_ = lean_box(0);
v___x_2647_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2626_, v___x_2645_, v___x_2639_, v___x_2644_, v___y_2628_, v___y_2629_);
lean_dec_ref_known(v___x_2639_, 7);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2655_; 
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v___x_2647_, 0);
lean_dec(v_unused_2656_);
v___x_2649_ = v___x_2647_;
v_isShared_2650_ = v_isSharedCheck_2655_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2647_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2655_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2651_ = lean_st_ref_get(v___x_2644_);
lean_dec(v___x_2644_);
lean_dec(v___x_2651_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2646_);
v___x_2653_ = v___x_2649_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2646_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_dec(v___x_2644_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2663_ == 0)
{
lean_object* v_unused_2664_; 
v_unused_2664_ = lean_ctor_get(v___x_2647_, 0);
lean_dec(v_unused_2664_);
v___x_2658_ = v___x_2647_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v___x_2647_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set_tag(v___x_2658_, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2646_);
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2646_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_a_2665_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2647_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2647_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v___x_2673_, lean_object* v_declName_2674_, lean_object* v_majorPos_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_2673_, v_declName_2674_, v_majorPos_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(uint8_t v___x_2680_, lean_object* v_env_2681_, lean_object* v_n_2682_, lean_object* v_x_2683_){
_start:
{
uint8_t v___x_2684_; 
v___x_2684_ = l_Lean_Environment_contains(v_env_2681_, v_n_2682_, v___x_2680_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v___x_2685_, lean_object* v_env_2686_, lean_object* v_n_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v___x_643__boxed_2689_; uint8_t v_res_2690_; lean_object* v_r_2691_; 
v___x_643__boxed_2689_ = lean_unbox(v___x_2685_);
v_res_2690_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_643__boxed_2689_, v_env_2686_, v_n_2687_, v_x_2688_);
lean_dec(v_x_2688_);
v_r_2691_ = lean_box(v_res_2690_);
return v_r_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_));
v___x_2720_ = l_Lean_registerParametricAttribute___redArg(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object* v_env_2723_, lean_object* v_declName_2724_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = l_Lean_Meta_recursorAttribute;
v___x_2727_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2725_, v___x_2726_, v_env_2723_, v_declName_2724_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo(lean_object* v_declName_2728_, lean_object* v_majorPos_x3f_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_st_ref_get(v_a_2733_);
if (lean_obj_tag(v_majorPos_x3f_2729_) == 0)
{
lean_object* v_env_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_env_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_env_2736_);
lean_dec(v___x_2735_);
lean_inc(v_declName_2728_);
v___x_2737_ = l_Lean_Meta_getMajorPos_x3f(v_env_2736_, v_declName_2728_);
v___x_2738_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2728_, v___x_2737_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; 
lean_dec(v___x_2735_);
v___x_2739_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(v_declName_2728_, v_majorPos_x3f_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo___boxed(lean_object* v_declName_2740_, lean_object* v_majorPos_x3f_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Meta_mkRecursorInfo(v_declName_2740_, v_majorPos_x3f_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2747_;
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
