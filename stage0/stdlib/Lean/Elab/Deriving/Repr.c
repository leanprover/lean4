// Lean compiler output
// Module: Lean.Elab.Deriving.Repr
// Imports: public import Lean.Meta.Inductive public import Lean.Elab.Deriving.Basic public import Lean.Elab.Deriving.Util
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Repr"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 59, 131, 233, 62, 241, 250, 220)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prec"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value),LEAN_SCALAR_PTR_LITERAL(178, 133, 204, 73, 239, 123, 12, 87)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 163, 238, 151, 160, 85, 71, 16)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\" := \""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\"_\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 44, 178, 157, 49, 38, 131, 220)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Format.group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(199, 101, 149, 40, 211, 134, 215, 211)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(244, 69, 187, 229, 60, 74, 115, 66)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(8, 121, 197, 203, 165, 174, 61, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(179, 146, 214, 149, 195, 116, 102, 235)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(248, 109, 138, 163, 21, 170, 71, 243)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\",\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.line"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 237, 177, 226, 131, 244, 212, 161)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 89, 162, 50, 159, 227, 59, 53)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Format.nil"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 110, 112, 1, 140, 132, 234, 227)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(38, 56, 177, 235, 80, 228, 131, 10)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Format.bracket"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bracket"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(174, 48, 2, 244, 180, 197, 18, 79)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(173, 181, 123, 51, 4, 114, 72, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\"{ \""};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\" }\""};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`deriving Repr` failed, unexpected number of fields in structure"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reprArg"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 167, 21, 149, 233, 224, 156, 221)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termMax_prec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 118, 206, 137, 233, 43, 182)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "max_prec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 42, 41, 58, 31, 42, 63)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 243, 205, 40, 12, 75, 164, 249)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.text"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Repr.addAppParen"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "addAppParen"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 59, 131, 233, 62, 241, 250, 220)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(81, 6, 140, 45, 150, 11, 23, 193)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≥_"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(58, 65, 30, 214, 7, 203, 184, 211)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ">="};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "no_expose"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value),LEAN_SCALAR_PTR_LITERAL(211, 61, 129, 110, 227, 154, 234, 3)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(224, 137, 43, 251, 2, 178, 60, 92)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 224, 49, 20, 188, 146, 89, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 160, 169, 100, 58, 75, 239, 18)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 81, 7, 4, 169, 73, 180)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(231, 58, 223, 30, 148, 240, 234, 38)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(225, 21, 194, 109, 33, 15, 109, 4)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 231, 73, 27, 250, 149, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 145, 209, 124, 47, 69, 201, 61)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 215, 65, 207, 88, 39, 128, 71)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 156, 16, 162, 242, 38, 216)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 90, 211, 79, 166, 122, 95, 47)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 118, 68, 66, 204, 66, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 138, 48, 165, 232, 217, 168, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1829928117) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 196, 216, 153, 78, 142, 253, 232)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 155, 187, 30, 146, 67, 38, 109)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 217, 197, 232, 108, 25, 15, 192)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 0, 128, 151, 4, 60, 211, 133)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10));
v___x_19_ = l_String_toRawSubstring_x27(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14));
v___x_25_ = l_String_toRawSubstring_x27(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Array_mkArray0___redArg();
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object* v_indVal_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = l_Lean_Elab_Deriving_mkHeader(v___x_52_, v___x_53_, v_indVal_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_toCold_55_; lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_103_; 
v_toCold_55_ = lean_ctor_get(v_a_49_, 0);
v_a_56_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_103_ == 0)
{
v___x_58_ = v___x_54_;
v_isShared_59_ = v_isSharedCheck_103_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_103_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_ref_60_; lean_object* v_quotContext_61_; lean_object* v_currMacroScope_62_; uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_binders_85_; lean_object* v_argNames_86_; lean_object* v_targetNames_87_; lean_object* v_targetType_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_102_; 
v_ref_60_ = lean_ctor_get(v_a_49_, 2);
v_quotContext_61_ = lean_ctor_get(v_toCold_55_, 8);
v_currMacroScope_62_ = lean_ctor_get(v_toCold_55_, 9);
v___x_63_ = 0;
v___x_64_ = l_Lean_SourceInfo_fromRef(v_ref_60_, v___x_63_);
v___x_65_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6));
v___x_66_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
lean_inc_n(v___x_64_, 7);
v___x_67_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_69_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_70_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
lean_inc_n(v_currMacroScope_62_, 2);
lean_inc_n(v_quotContext_61_, 2);
v___x_71_ = l_Lean_addMacroScope(v_quotContext_61_, v___x_70_, v_currMacroScope_62_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_73_, 0, v___x_64_);
lean_ctor_set(v___x_73_, 1, v___x_69_);
lean_ctor_set(v___x_73_, 2, v___x_71_);
lean_ctor_set(v___x_73_, 3, v___x_72_);
v___x_74_ = l_Lean_Syntax_node1(v___x_64_, v___x_68_, v___x_73_);
v___x_75_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_76_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_64_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15);
v___x_78_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16));
v___x_79_ = l_Lean_addMacroScope(v_quotContext_61_, v___x_78_, v_currMacroScope_62_);
v___x_80_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21));
v___x_81_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_81_, 0, v___x_64_);
lean_ctor_set(v___x_81_, 1, v___x_77_);
lean_ctor_set(v___x_81_, 2, v___x_79_);
lean_ctor_set(v___x_81_, 3, v___x_80_);
v___x_82_ = l_Lean_Syntax_node2(v___x_64_, v___x_68_, v___x_76_, v___x_81_);
v___x_83_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_84_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_84_, 0, v___x_64_);
lean_ctor_set(v___x_84_, 1, v___x_68_);
lean_ctor_set(v___x_84_, 2, v___x_83_);
v_binders_85_ = lean_ctor_get(v_a_56_, 0);
v_argNames_86_ = lean_ctor_get(v_a_56_, 1);
v_targetNames_87_ = lean_ctor_get(v_a_56_, 2);
v_targetType_88_ = lean_ctor_get(v_a_56_, 3);
v_isSharedCheck_102_ = !lean_is_exclusive(v_a_56_);
if (v_isSharedCheck_102_ == 0)
{
v___x_90_ = v_a_56_;
v_isShared_91_ = v_isSharedCheck_102_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_targetType_88_);
lean_inc(v_targetNames_87_);
lean_inc(v_argNames_86_);
lean_inc(v_binders_85_);
lean_dec(v_a_56_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_102_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_92_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
lean_inc(v___x_64_);
v___x_93_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_64_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_Syntax_node5(v___x_64_, v___x_65_, v___x_67_, v___x_74_, v___x_82_, v___x_84_, v___x_93_);
v___x_95_ = lean_array_push(v_binders_85_, v___x_94_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_95_);
v___x_97_ = v___x_90_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_argNames_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_targetNames_87_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_targetType_88_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_97_);
v___x_99_ = v___x_58_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
else
{
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object* v_indVal_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(lean_object* v_k_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v_b_116_, lean_object* v_c_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
v___x_123_ = lean_apply_9(v_k_113_, v_b_116_, v_c_117_, v___y_114_, v___y_115_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, lean_box(0));
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed(lean_object* v_k_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v_b_127_, lean_object* v_c_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(v_k_124_, v___y_125_, v___y_126_, v_b_127_, v_c_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(lean_object* v_type_135_, lean_object* v_k_136_, uint8_t v_cleanupAnnotations_137_, uint8_t v_whnfType_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___f_146_; lean_object* v___x_147_; 
lean_inc(v___y_140_);
lean_inc_ref(v___y_139_);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_146_, 0, v_k_136_);
lean_closure_set(v___f_146_, 1, v___y_139_);
lean_closure_set(v___f_146_, 2, v___y_140_);
v___x_147_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_135_, v___f_146_, v_cleanupAnnotations_137_, v_whnfType_138_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
if (lean_obj_tag(v___x_147_) == 0)
{
return v___x_147_;
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___boxed(lean_object* v_type_156_, lean_object* v_k_157_, lean_object* v_cleanupAnnotations_158_, lean_object* v_whnfType_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_167_; uint8_t v_whnfType_boxed_168_; lean_object* v_res_169_; 
v_cleanupAnnotations_boxed_167_ = lean_unbox(v_cleanupAnnotations_158_);
v_whnfType_boxed_168_ = lean_unbox(v_whnfType_159_);
v_res_169_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_156_, v_k_157_, v_cleanupAnnotations_boxed_167_, v_whnfType_boxed_168_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(lean_object* v_00_u03b1_170_, lean_object* v_type_171_, lean_object* v_k_172_, uint8_t v_cleanupAnnotations_173_, uint8_t v_whnfType_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_171_, v_k_172_, v_cleanupAnnotations_173_, v_whnfType_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___boxed(lean_object* v_00_u03b1_183_, lean_object* v_type_184_, lean_object* v_k_185_, lean_object* v_cleanupAnnotations_186_, lean_object* v_whnfType_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_195_; uint8_t v_whnfType_boxed_196_; lean_object* v_res_197_; 
v_cleanupAnnotations_boxed_195_ = lean_unbox(v_cleanupAnnotations_186_);
v_whnfType_boxed_196_ = lean_unbox(v_whnfType_187_);
v_res_197_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(v_00_u03b1_183_, v_type_184_, v_k_185_, v_cleanupAnnotations_boxed_195_, v_whnfType_boxed_196_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_197_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_box(1);
v___x_199_ = l_Lean_MessageData_ofFormat(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2));
v___x_204_ = l_Lean_MessageData_ofFormat(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
return v_x_205_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_230_; 
v_head_207_ = lean_ctor_get(v_x_206_, 0);
v_tail_208_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_230_ == 0)
{
v___x_210_ = v_x_206_;
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_head_207_);
lean_dec(v_x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_before_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_228_; 
v_before_212_ = lean_ctor_get(v_head_207_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_head_207_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_head_207_, 1);
lean_dec(v_unused_229_);
v___x_214_ = v_head_207_;
v_isShared_215_ = v_isSharedCheck_228_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_before_212_);
lean_dec(v_head_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_228_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 7);
lean_ctor_set(v___x_214_, 1, v___x_216_);
lean_ctor_set(v___x_214_, 0, v_x_205_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_x_205_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_227_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 7);
lean_ctor_set(v___x_210_, 1, v___x_219_);
lean_ctor_set(v___x_210_, 0, v___x_218_);
v___x_221_ = v___x_210_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_226_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_MessageData_ofSyntax(v_before_212_);
v___x_223_ = l_Lean_indentD(v___x_222_);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_221_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v_x_205_ = v___x_224_;
v_x_206_ = v_tail_208_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(lean_object* v_opts_231_, lean_object* v_opt_232_){
_start:
{
lean_object* v_name_233_; lean_object* v_defValue_234_; lean_object* v_map_235_; lean_object* v___x_236_; 
v_name_233_ = lean_ctor_get(v_opt_232_, 0);
v_defValue_234_ = lean_ctor_get(v_opt_232_, 1);
v_map_235_ = lean_ctor_get(v_opts_231_, 0);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_235_, v_name_233_);
if (lean_obj_tag(v___x_236_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = lean_unbox(v_defValue_234_);
return v___x_237_;
}
else
{
lean_object* v_val_238_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_236_, 1);
if (lean_obj_tag(v_val_238_) == 1)
{
uint8_t v_v_239_; 
v_v_239_ = lean_ctor_get_uint8(v_val_238_, 0);
lean_dec_ref_known(v_val_238_, 0);
return v_v_239_;
}
else
{
uint8_t v___x_240_; 
lean_dec(v_val_238_);
v___x_240_ = lean_unbox(v_defValue_234_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_241_, lean_object* v_opt_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_opts_241_, v_opt_242_);
lean_dec_ref(v_opt_242_);
lean_dec_ref(v_opts_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1));
v___x_249_ = l_Lean_MessageData_ofFormat(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(lean_object* v_msgData_250_, lean_object* v_macroStack_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_254_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_252_);
v___x_255_ = l_Lean_Elab_pp_macroStack;
v___x_256_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v___x_254_, v___x_255_);
lean_dec_ref(v___x_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_macroStack_251_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_msgData_250_);
return v___x_257_;
}
else
{
if (lean_obj_tag(v_macroStack_251_) == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_msgData_250_);
return v___x_258_;
}
else
{
lean_object* v_head_259_; lean_object* v_after_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_275_; 
v_head_259_ = lean_ctor_get(v_macroStack_251_, 0);
lean_inc(v_head_259_);
v_after_260_ = lean_ctor_get(v_head_259_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_head_259_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_head_259_, 0);
lean_dec(v_unused_276_);
v___x_262_ = v_head_259_;
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_after_260_);
lean_dec(v_head_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 7);
lean_ctor_set(v___x_262_, 1, v___x_264_);
lean_ctor_set(v___x_262_, 0, v_msgData_250_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_msgData_250_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_274_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_msgData_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_MessageData_ofSyntax(v_after_260_);
v___x_270_ = l_Lean_indentD(v___x_269_);
v_msgData_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_271_, 0, v___x_268_);
lean_ctor_set(v_msgData_271_, 1, v___x_270_);
v___x_272_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(v_msgData_271_, v_macroStack_251_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_277_, lean_object* v_macroStack_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_277_, v_macroStack_278_, v___y_279_);
lean_dec_ref(v___y_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; uint8_t v___x_290_; lean_object* v_env_291_; lean_object* v___x_292_; lean_object* v_toCold_293_; lean_object* v_mctx_294_; lean_object* v_lctx_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = 0;
v_env_291_ = l_Lean_Environment_setRecordingDeps(v_env_289_, v___x_290_);
v___x_292_ = lean_st_ref_get(v___y_284_);
v_toCold_293_ = lean_ctor_get(v___y_285_, 0);
v_mctx_294_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_292_);
v_lctx_295_ = lean_ctor_get(v___y_283_, 2);
v_options_296_ = lean_ctor_get(v_toCold_293_, 2);
lean_inc_ref(v_options_296_);
lean_inc_ref(v_lctx_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v_env_291_);
lean_ctor_set(v___x_297_, 1, v_mctx_294_);
lean_ctor_set(v___x_297_, 2, v_lctx_295_);
lean_ctor_set(v___x_297_, 3, v_options_296_);
v___x_298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_msgData_282_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4___boxed(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_ref_315_; lean_object* v_macroStack_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_ref_315_ = lean_ctor_get(v___y_312_, 2);
v_macroStack_316_ = lean_ctor_get(v___y_308_, 1);
v___x_317_ = l_Lean_Elab_getBetterRef(v_ref_315_, v_macroStack_316_);
v___x_318_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_307_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
lean_inc(v_macroStack_316_);
v___x_320_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_a_319_, v_macroStack_316_, v___y_312_);
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_317_);
lean_ctor_set(v___x_325_, 1, v_a_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 1);
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object* v_msg_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v_a_341_, lean_object* v_b_342_){
_start:
{
uint8_t v_decide_343_; 
v_decide_343_ = lean_nat_dec_eq(v_a_341_, v___x_339_);
if (v_decide_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_string_utf8_next_fast(v___x_340_, v_a_341_);
lean_dec(v_a_341_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_b_342_, v___x_345_);
lean_dec(v_b_342_);
v_a_341_ = v___x_344_;
v_b_342_ = v___x_346_;
goto _start;
}
else
{
lean_dec(v_a_341_);
return v_b_342_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_a_350_, lean_object* v_b_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_348_, v___x_349_, v_a_350_, v_b_351_);
lean_dec_ref(v___x_349_);
lean_dec(v___x_348_);
return v_res_352_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13));
v___x_379_ = l_String_toRawSubstring_x27(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33));
v___x_426_ = l_String_toRawSubstring_x27(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43));
v___x_449_ = l_String_toRawSubstring_x27(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52));
v___x_471_ = l_String_toRawSubstring_x27(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(lean_object* v___f_487_, lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v_____r_495_, lean_object* v_fields_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_536_; 
lean_inc_ref(v___x_489_);
v___x_536_ = l_Lean_Meta_isType(v___x_489_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; uint8_t v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = lean_unbox(v_a_537_);
lean_dec(v_a_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_isProof(v___x_489_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; uint8_t v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = lean_unbox(v_a_540_);
lean_dec(v_a_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_542_ = lean_string_utf8_byte_size(v___x_490_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_542_, v___x_490_, v___x_543_, v___x_491_);
v___x_545_ = lean_unsigned_to_nat(4u);
v___x_546_ = lean_nat_add(v___x_544_, v___x_545_);
lean_dec(v___x_544_);
v___x_547_ = l_Nat_reprFast(v___x_546_);
v___x_548_ = l_Lean_Syntax_mkNumLit(v___x_547_, v___x_492_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_549_ = lean_apply_7(v___f_487_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_toCold_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_617_; 
v_toCold_550_ = lean_ctor_get(v___y_501_, 0);
v_a_551_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_617_ == 0)
{
v___x_553_ = v___x_549_;
v_isShared_554_ = v_isSharedCheck_617_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_617_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_quotContext_555_; lean_object* v_currMacroScope_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v_quotContext_555_ = lean_ctor_get(v_toCold_550_, 8);
v_currMacroScope_556_ = lean_ctor_get(v_toCold_550_, 9);
v___x_557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_551_, 25);
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v_a_551_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
lean_inc_ref_n(v___x_559_, 2);
v___x_560_ = l_Lean_Syntax_node3(v_a_551_, v___x_557_, v_fields_496_, v___x_559_, v___x_488_);
v___x_561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_562_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5));
v___x_563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_563_, 0, v_a_551_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = l_Lean_Syntax_node1(v_a_551_, v___x_561_, v___x_563_);
v___x_565_ = l_Lean_Syntax_node3(v_a_551_, v___x_557_, v___x_560_, v___x_559_, v___x_564_);
v___x_566_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8));
v___x_567_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10));
v___x_568_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v_a_551_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12));
v___x_571_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14);
v___x_572_ = lean_box(0);
lean_inc_n(v_currMacroScope_556_, 4);
lean_inc_n(v_quotContext_555_, 4);
v___x_573_ = l_Lean_addMacroScope(v_quotContext_555_, v___x_572_, v_currMacroScope_556_);
v___x_574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30));
v___x_575_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_575_, 0, v_a_551_);
lean_ctor_set(v___x_575_, 1, v___x_571_);
lean_ctor_set(v___x_575_, 2, v___x_573_);
lean_ctor_set(v___x_575_, 3, v___x_574_);
v___x_576_ = l_Lean_Syntax_node1(v_a_551_, v___x_570_, v___x_575_);
v___x_577_ = l_Lean_Syntax_node2(v_a_551_, v___x_567_, v___x_569_, v___x_576_);
v___x_578_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32));
v___x_579_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34);
v___x_580_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37));
v___x_581_ = l_Lean_addMacroScope(v_quotContext_555_, v___x_580_, v_currMacroScope_556_);
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42));
v___x_583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_583_, 0, v_a_551_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
lean_ctor_set(v___x_583_, 2, v___x_581_);
lean_ctor_set(v___x_583_, 3, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44);
v___x_586_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46));
v___x_587_ = l_Lean_addMacroScope(v_quotContext_555_, v___x_586_, v_currMacroScope_556_);
v___x_588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51));
v___x_589_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_589_, 0, v_a_551_);
lean_ctor_set(v___x_589_, 1, v___x_585_);
lean_ctor_set(v___x_589_, 2, v___x_587_);
lean_ctor_set(v___x_589_, 3, v___x_588_);
v___x_590_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53);
v___x_591_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54));
v___x_592_ = l_Lean_addMacroScope(v_quotContext_555_, v___x_591_, v_currMacroScope_556_);
v___x_593_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56));
v___x_594_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_594_, 0, v_a_551_);
lean_ctor_set(v___x_594_, 1, v___x_590_);
lean_ctor_set(v___x_594_, 2, v___x_592_);
lean_ctor_set(v___x_594_, 3, v___x_593_);
v___x_595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58));
v___x_596_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v_a_551_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_mkIdent(v___x_493_);
v___x_599_ = l_Lean_Syntax_node3(v_a_551_, v___x_595_, v___x_494_, v___x_597_, v___x_598_);
v___x_600_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v_a_551_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_inc_ref_n(v___x_601_, 3);
lean_inc_n(v___x_577_, 3);
v___x_602_ = l_Lean_Syntax_node3(v_a_551_, v___x_566_, v___x_577_, v___x_599_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v_a_551_, v___x_584_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node2(v_a_551_, v___x_578_, v___x_594_, v___x_603_);
v___x_605_ = l_Lean_Syntax_node3(v_a_551_, v___x_566_, v___x_577_, v___x_604_, v___x_601_);
v___x_606_ = l_Lean_Syntax_node2(v_a_551_, v___x_584_, v___x_548_, v___x_605_);
v___x_607_ = l_Lean_Syntax_node2(v_a_551_, v___x_578_, v___x_589_, v___x_606_);
v___x_608_ = l_Lean_Syntax_node3(v_a_551_, v___x_566_, v___x_577_, v___x_607_, v___x_601_);
v___x_609_ = l_Lean_Syntax_node1(v_a_551_, v___x_584_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node2(v_a_551_, v___x_578_, v___x_583_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node3(v_a_551_, v___x_566_, v___x_577_, v___x_610_, v___x_601_);
v___x_612_ = l_Lean_Syntax_node3(v_a_551_, v___x_557_, v___x_565_, v___x_559_, v___x_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_613_);
v___x_615_ = v___x_553_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v___x_548_);
lean_dec(v_fields_496_);
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_488_);
v_a_618_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_549_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_549_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
goto v___jp_504_;
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_fields_496_);
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec(v___x_488_);
lean_dec_ref(v___f_487_);
v_a_626_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_539_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_539_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec_ref(v___x_489_);
goto v___jp_504_;
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_fields_496_);
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec_ref(v___x_489_);
lean_dec(v___x_488_);
lean_dec_ref(v___f_487_);
v_a_634_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_536_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_536_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
v___jp_504_:
{
lean_object* v___x_505_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_505_ = lean_apply_7(v___f_487_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_527_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_527_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_527_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_527_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_510_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_511_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_506_, 7);
v___x_512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_512_, 0, v_a_506_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
lean_inc_ref_n(v___x_512_, 2);
v___x_513_ = l_Lean_Syntax_node3(v_a_506_, v___x_510_, v_fields_496_, v___x_512_, v___x_488_);
v___x_514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_515_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5));
v___x_516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_516_, 0, v_a_506_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_Syntax_node1(v_a_506_, v___x_514_, v___x_516_);
v___x_518_ = l_Lean_Syntax_node3(v_a_506_, v___x_510_, v___x_513_, v___x_512_, v___x_517_);
v___x_519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_520_, 0, v_a_506_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_Syntax_node1(v_a_506_, v___x_514_, v___x_520_);
v___x_522_ = l_Lean_Syntax_node3(v_a_506_, v___x_510_, v___x_518_, v___x_512_, v___x_521_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_523_);
v___x_525_ = v___x_508_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_fields_496_);
lean_dec(v___x_488_);
v_a_528_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_505_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_505_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___f_642_ = _args[0];
lean_object* v___x_643_ = _args[1];
lean_object* v___x_644_ = _args[2];
lean_object* v___x_645_ = _args[3];
lean_object* v___x_646_ = _args[4];
lean_object* v___x_647_ = _args[5];
lean_object* v___x_648_ = _args[6];
lean_object* v___x_649_ = _args[7];
lean_object* v_____r_650_ = _args[8];
lean_object* v_fields_651_ = _args[9];
lean_object* v___y_652_ = _args[10];
lean_object* v___y_653_ = _args[11];
lean_object* v___y_654_ = _args[12];
lean_object* v___y_655_ = _args[13];
lean_object* v___y_656_ = _args[14];
lean_object* v___y_657_ = _args[15];
lean_object* v___y_658_ = _args[16];
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_642_, v___x_643_, v___x_644_, v___x_645_, v___x_646_, v___x_647_, v___x_648_, v___x_649_, v_____r_650_, v_fields_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v___x_645_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_ref_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_ref_667_ = lean_ctor_get(v___y_664_, 2);
v___x_668_ = 0;
v___x_669_ = l_Lean_SourceInfo_fromRef(v_ref_667_, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed(lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_678_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2));
v___x_683_ = l_String_toRawSubstring_x27(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object* v_upperBound_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v_xs_706_, lean_object* v___x_707_, lean_object* v_a_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___y_718_; uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_lt(v_a_708_, v_upperBound_703_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v_a_708_);
lean_dec(v___x_707_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_b_709_);
return v___x_741_;
}
else
{
lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___f_742_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0));
v___x_743_ = l_Lean_instInhabitedExpr;
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_fget_borrowed(v___x_704_, v_a_708_);
lean_inc(v___x_745_);
v___x_746_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_745_, v___x_740_);
v___x_747_ = lean_box(2);
lean_inc_ref(v___x_746_);
v___x_748_ = l_Lean_Syntax_mkStrLit(v___x_746_, v___x_747_);
v___x_749_ = lean_nat_add(v___x_705_, v_a_708_);
v___x_750_ = lean_array_get_borrowed(v___x_743_, v_xs_706_, v___x_749_);
lean_dec(v___x_749_);
v___x_751_ = lean_nat_dec_eq(v_a_708_, v___x_744_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_toCold_753_; lean_object* v_a_754_; lean_object* v_quotContext_755_; lean_object* v_currMacroScope_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_toCold_753_ = lean_ctor_get(v___y_714_, 0);
v_a_754_ = lean_ctor_get(v___x_752_, 0);
lean_inc_n(v_a_754_, 6);
lean_dec_ref_known(v___x_752_, 1);
v_quotContext_755_ = lean_ctor_get(v_toCold_753_, 8);
v_currMacroScope_756_ = lean_ctor_get(v_toCold_753_, 9);
v___x_757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_758_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v_a_754_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_754_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v_a_754_, v___x_760_, v___x_762_);
lean_inc_ref(v___x_759_);
v___x_764_ = l_Lean_Syntax_node3(v_a_754_, v___x_757_, v_b_709_, v___x_759_, v___x_763_);
v___x_765_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_756_);
lean_inc(v_quotContext_755_);
v___x_767_ = l_Lean_addMacroScope(v_quotContext_755_, v___x_766_, v_currMacroScope_756_);
v___x_768_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_769_, 0, v_a_754_);
lean_ctor_set(v___x_769_, 1, v___x_765_);
lean_ctor_set(v___x_769_, 2, v___x_767_);
lean_ctor_set(v___x_769_, 3, v___x_768_);
v___x_770_ = l_Lean_Syntax_node3(v_a_754_, v___x_757_, v___x_764_, v___x_759_, v___x_769_);
v___x_771_ = lean_box(0);
lean_inc(v___x_707_);
lean_inc(v___x_745_);
lean_inc(v___x_750_);
v___x_772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_742_, v___x_748_, v___x_750_, v___x_746_, v___x_744_, v___x_747_, v___x_745_, v___x_707_, v___x_771_, v___x_770_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec_ref(v___x_746_);
v___y_718_ = v___x_772_;
goto v___jp_717_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v___x_748_);
lean_dec_ref(v___x_746_);
lean_dec(v_b_709_);
lean_dec(v_a_708_);
lean_dec(v___x_707_);
v_a_773_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_752_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_752_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_box(0);
lean_inc(v___x_707_);
lean_inc(v___x_745_);
lean_inc(v___x_750_);
v___x_782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_742_, v___x_748_, v___x_750_, v___x_746_, v___x_744_, v___x_747_, v___x_745_, v___x_707_, v___x_781_, v_b_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec_ref(v___x_746_);
v___y_718_ = v___x_782_;
goto v___jp_717_;
}
}
v___jp_717_:
{
if (lean_obj_tag(v___y_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_731_; 
v_a_719_ = lean_ctor_get(v___y_718_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___y_718_);
if (v_isSharedCheck_731_ == 0)
{
v___x_721_ = v___y_718_;
v_isShared_722_ = v_isSharedCheck_731_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___y_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_731_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
if (lean_obj_tag(v_a_719_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; 
lean_dec(v_a_708_);
lean_dec(v___x_707_);
v_a_723_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v_a_719_, 1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_a_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_del_object(v___x_721_);
v_a_727_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v_a_719_, 1);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_a_708_, v___x_728_);
lean_dec(v_a_708_);
v_a_708_ = v___x_729_;
v_b_709_ = v_a_727_;
goto _start;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_708_);
lean_dec(v___x_707_);
v_a_732_ = lean_ctor_get(v___y_718_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___y_718_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___y_718_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___y_718_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object* v_upperBound_783_, lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_xs_786_, lean_object* v___x_787_, lean_object* v_a_788_, lean_object* v_b_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_783_, v___x_784_, v___x_785_, v_xs_786_, v___x_787_, v_a_788_, v_b_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec_ref(v_xs_786_);
lean_dec(v___x_785_);
lean_dec_ref(v___x_784_);
lean_dec(v_upperBound_783_);
return v_res_797_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0));
v___x_800_ = l_String_toRawSubstring_x27(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9));
v___x_822_ = l_String_toRawSubstring_x27(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object* v___x_842_, lean_object* v_numParams_843_, lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v_xs_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_toCold_855_; lean_object* v_ref_856_; lean_object* v_quotContext_857_; lean_object* v_currMacroScope_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_toCold_855_ = lean_ctor_get(v___y_852_, 0);
v_ref_856_ = lean_ctor_get(v___y_852_, 2);
v_quotContext_857_ = lean_ctor_get(v_toCold_855_, 8);
v_currMacroScope_858_ = lean_ctor_get(v_toCold_855_, 9);
v___x_859_ = 0;
v___x_860_ = l_Lean_SourceInfo_fromRef(v_ref_856_, v___x_859_);
v___x_861_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3));
lean_inc(v_currMacroScope_858_);
lean_inc(v_quotContext_857_);
v___x_863_ = l_Lean_addMacroScope(v_quotContext_857_, v___x_862_, v_currMacroScope_858_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8));
v___x_865_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_865_, 0, v___x_860_);
lean_ctor_set(v___x_865_, 1, v___x_861_);
lean_ctor_set(v___x_865_, 2, v___x_863_);
lean_ctor_set(v___x_865_, 3, v___x_864_);
v___x_904_ = lean_array_get_size(v_xs_846_);
v___x_905_ = lean_array_get_size(v___x_842_);
v___x_906_ = lean_nat_add(v_numParams_843_, v___x_905_);
v___x_907_ = lean_nat_dec_eq(v___x_904_, v___x_906_);
lean_dec(v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref_known(v___x_865_, 4);
lean_dec(v___x_845_);
lean_dec(v___x_844_);
v___x_908_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19);
v___x_909_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_908_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
v___y_867_ = v___y_848_;
v___y_868_ = v___y_849_;
v___y_869_ = v___y_850_;
v___y_870_ = v___y_851_;
v___y_871_ = v___y_852_;
v___y_872_ = v___y_853_;
goto v___jp_866_;
}
v___jp_866_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_array_get_size(v___x_842_);
v___x_874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v___x_873_, v___x_842_, v_numParams_843_, v_xs_846_, v___x_844_, v___x_845_, v___x_865_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_toCold_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_903_; 
v_toCold_875_ = lean_ctor_get(v___y_871_, 0);
v_a_876_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_903_ == 0)
{
v___x_878_ = v___x_874_;
v_isShared_879_ = v_isSharedCheck_903_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_903_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_ref_880_; lean_object* v_quotContext_881_; lean_object* v_currMacroScope_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v_ref_880_ = lean_ctor_get(v___y_871_, 2);
v_quotContext_881_ = lean_ctor_get(v_toCold_875_, 8);
v_currMacroScope_882_ = lean_ctor_get(v_toCold_875_, 9);
v___x_883_ = l_Lean_SourceInfo_fromRef(v_ref_880_, v___x_859_);
v___x_884_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32));
v___x_885_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10);
v___x_886_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12));
lean_inc(v_currMacroScope_882_);
lean_inc(v_quotContext_881_);
v___x_887_ = l_Lean_addMacroScope(v_quotContext_881_, v___x_886_, v_currMacroScope_882_);
v___x_888_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15));
lean_inc_n(v___x_883_, 6);
v___x_889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_889_, 0, v___x_883_);
lean_ctor_set(v___x_889_, 1, v___x_885_);
lean_ctor_set(v___x_889_, 2, v___x_887_);
lean_ctor_set(v___x_889_, 3, v___x_888_);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_892_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16));
v___x_893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_883_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Lean_Syntax_node1(v___x_883_, v___x_891_, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17));
v___x_896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_883_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_Syntax_node1(v___x_883_, v___x_891_, v___x_896_);
v___x_898_ = l_Lean_Syntax_node3(v___x_883_, v___x_890_, v___x_894_, v_a_876_, v___x_897_);
v___x_899_ = l_Lean_Syntax_node2(v___x_883_, v___x_884_, v___x_889_, v___x_898_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_899_);
v___x_901_ = v___x_878_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
else
{
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object* v___x_918_, lean_object* v_numParams_919_, lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v_xs_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(v___x_918_, v_numParams_919_, v___x_920_, v___x_921_, v_xs_922_, v_x_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v_x_923_);
lean_dec_ref(v_xs_922_);
lean_dec(v_numParams_919_);
lean_dec_ref(v___x_918_);
return v_res_931_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_instMonadEIO___redArg();
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object* v_msg_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_toApplicative_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_1040_; 
v___x_947_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0);
v___x_948_ = l_StateRefT_x27_instMonad___redArg(v___x_947_);
v_toApplicative_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v___x_948_, 1);
lean_dec(v_unused_1041_);
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_1040_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_toApplicative_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_1040_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_toFunctor_953_; lean_object* v_toSeq_954_; lean_object* v_toSeqLeft_955_; lean_object* v_toSeqRight_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1038_; 
v_toFunctor_953_ = lean_ctor_get(v_toApplicative_949_, 0);
v_toSeq_954_ = lean_ctor_get(v_toApplicative_949_, 2);
v_toSeqLeft_955_ = lean_ctor_get(v_toApplicative_949_, 3);
v_toSeqRight_956_ = lean_ctor_get(v_toApplicative_949_, 4);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_toApplicative_949_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v_toApplicative_949_, 1);
lean_dec(v_unused_1039_);
v___x_958_ = v_toApplicative_949_;
v_isShared_959_ = v_isSharedCheck_1038_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_toSeqRight_956_);
lean_inc(v_toSeqLeft_955_);
lean_inc(v_toSeq_954_);
lean_inc(v_toFunctor_953_);
lean_dec(v_toApplicative_949_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1038_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___f_962_; lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___x_969_; 
v___f_960_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1));
v___f_961_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_953_);
v___f_962_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_962_, 0, v_toFunctor_953_);
v___f_963_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_963_, 0, v_toFunctor_953_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___f_962_);
lean_ctor_set(v___x_964_, 1, v___f_963_);
v___f_965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_965_, 0, v_toSeqRight_956_);
v___f_966_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_966_, 0, v_toSeqLeft_955_);
v___f_967_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_967_, 0, v_toSeq_954_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 4, v___f_965_);
lean_ctor_set(v___x_958_, 3, v___f_966_);
lean_ctor_set(v___x_958_, 2, v___f_967_);
lean_ctor_set(v___x_958_, 1, v___f_960_);
lean_ctor_set(v___x_958_, 0, v___x_964_);
v___x_969_ = v___x_958_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___f_960_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v___f_967_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v___f_966_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v___f_965_);
v___x_969_ = v_reuseFailAlloc_1037_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___f_961_);
lean_ctor_set(v___x_951_, 0, v___x_969_);
v___x_971_ = v___x_951_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___f_961_);
v___x_971_ = v_reuseFailAlloc_1036_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v_toApplicative_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1034_; 
v___x_972_ = l_StateRefT_x27_instMonad___redArg(v___x_971_);
v_toApplicative_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v___x_972_, 1);
lean_dec(v_unused_1035_);
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1034_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_toApplicative_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1034_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_toFunctor_977_; lean_object* v_toSeq_978_; lean_object* v_toSeqLeft_979_; lean_object* v_toSeqRight_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1032_; 
v_toFunctor_977_ = lean_ctor_get(v_toApplicative_973_, 0);
v_toSeq_978_ = lean_ctor_get(v_toApplicative_973_, 2);
v_toSeqLeft_979_ = lean_ctor_get(v_toApplicative_973_, 3);
v_toSeqRight_980_ = lean_ctor_get(v_toApplicative_973_, 4);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_toApplicative_973_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_toApplicative_973_, 1);
lean_dec(v_unused_1033_);
v___x_982_ = v_toApplicative_973_;
v_isShared_983_ = v_isSharedCheck_1032_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_toSeqRight_980_);
lean_inc(v_toSeqLeft_979_);
lean_inc(v_toSeq_978_);
lean_inc(v_toFunctor_977_);
lean_dec(v_toApplicative_973_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1032_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___x_993_; 
v___f_984_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3));
v___f_985_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_977_);
v___f_986_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_986_, 0, v_toFunctor_977_);
v___f_987_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_987_, 0, v_toFunctor_977_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___f_986_);
lean_ctor_set(v___x_988_, 1, v___f_987_);
v___f_989_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_989_, 0, v_toSeqRight_980_);
v___f_990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_990_, 0, v_toSeqLeft_979_);
v___f_991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_991_, 0, v_toSeq_978_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v___f_989_);
lean_ctor_set(v___x_982_, 3, v___f_990_);
lean_ctor_set(v___x_982_, 2, v___f_991_);
lean_ctor_set(v___x_982_, 1, v___f_984_);
lean_ctor_set(v___x_982_, 0, v___x_988_);
v___x_993_ = v___x_982_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___f_984_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v___f_991_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v___f_990_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v___f_989_);
v___x_993_ = v_reuseFailAlloc_1031_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v___f_985_);
lean_ctor_set(v___x_975_, 0, v___x_993_);
v___x_995_ = v___x_975_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___f_985_);
v___x_995_ = v_reuseFailAlloc_1030_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v_toApplicative_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1028_; 
v___x_996_ = l_StateRefT_x27_instMonad___redArg(v___x_995_);
v_toApplicative_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_996_, 1);
lean_dec(v_unused_1029_);
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1028_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_toApplicative_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1028_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_toFunctor_1001_; lean_object* v_toSeq_1002_; lean_object* v_toSeqLeft_1003_; lean_object* v_toSeqRight_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1026_; 
v_toFunctor_1001_ = lean_ctor_get(v_toApplicative_997_, 0);
v_toSeq_1002_ = lean_ctor_get(v_toApplicative_997_, 2);
v_toSeqLeft_1003_ = lean_ctor_get(v_toApplicative_997_, 3);
v_toSeqRight_1004_ = lean_ctor_get(v_toApplicative_997_, 4);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_toApplicative_997_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_toApplicative_997_, 1);
lean_dec(v_unused_1027_);
v___x_1006_ = v_toApplicative_997_;
v_isShared_1007_ = v_isSharedCheck_1026_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_toSeqRight_1004_);
lean_inc(v_toSeqLeft_1003_);
lean_inc(v_toSeq_1002_);
lean_inc(v_toFunctor_1001_);
lean_dec(v_toApplicative_997_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1026_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1017_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5));
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6));
lean_inc_ref(v_toFunctor_1001_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toFunctor_1001_);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toFunctor_1001_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___f_1010_);
lean_ctor_set(v___x_1012_, 1, v___f_1011_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toSeqRight_1004_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toSeqLeft_1003_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toSeq_1002_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 4, v___f_1013_);
lean_ctor_set(v___x_1006_, 3, v___f_1014_);
lean_ctor_set(v___x_1006_, 2, v___f_1015_);
lean_ctor_set(v___x_1006_, 1, v___f_1008_);
lean_ctor_set(v___x_1006_, 0, v___x_1012_);
v___x_1017_ = v___x_1006_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___f_1008_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v___f_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v___f_1014_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v___f_1013_);
v___x_1017_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v___f_1009_);
lean_ctor_set(v___x_999_, 0, v___x_1017_);
v___x_1019_ = v___x_999_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___f_1009_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_19743__overap_1022_; lean_object* v___x_1023_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = l_instInhabitedOfMonad___redArg(v___x_1019_, v___x_1020_);
v___x_19743__overap_1022_ = lean_panic_fn_borrowed(v___x_1021_, v_msg_939_);
lean_dec(v___x_1021_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
v___x_1023_ = lean_apply_7(v___x_19743__overap_1022_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, lean_box(0));
return v___x_1023_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1050_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6));
v___x_1061_ = lean_unsigned_to_nat(11u);
v___x_1062_ = lean_unsigned_to_nat(122u);
v___x_1063_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5));
v___x_1064_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4));
v___x_1065_ = l_mkPanicMessageWithDecl(v___x_1064_, v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object* v_constName_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1082_; lean_object* v_env_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = lean_st_ref_get(v___y_1072_);
v_env_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_env_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = 0;
lean_inc(v_constName_1066_);
v___x_1085_ = l_Lean_Environment_findAsync_x3f(v_env_1083_, v_constName_1066_, v___x_1084_);
if (lean_obj_tag(v___x_1085_) == 1)
{
lean_object* v_val_1086_; uint8_t v_kind_1087_; 
v_val_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v_kind_1087_ = lean_ctor_get_uint8(v_val_1086_, sizeof(void*)*3);
if (v_kind_1087_ == 6)
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1086_);
if (lean_obj_tag(v___x_1088_) == 6)
{
lean_object* v_val_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_constName_1066_);
v_val_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_val_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 0);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_val_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v___x_1088_);
v___x_1097_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7);
v___x_1098_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v___x_1097_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
if (lean_obj_tag(v_a_1099_) == 0)
{
lean_del_object(v___x_1101_);
goto v___jp_1074_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; 
lean_dec(v_constName_1066_);
v_val_1103_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v_a_1099_, 1);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_val_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_constName_1066_);
v_a_1108_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1098_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1098_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
else
{
lean_dec(v_val_1086_);
goto v___jp_1074_;
}
}
else
{
lean_dec(v___x_1085_);
goto v___jp_1074_;
}
v___jp_1074_:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1075_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1);
v___x_1076_ = 0;
v___x_1077_ = l_Lean_MessageData_ofConstName(v_constName_1066_, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1075_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_1080_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object* v_constName_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_constName_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object* v_header_1125_, lean_object* v_indVal_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_toConstantVal_1134_; lean_object* v_numParams_1135_; lean_object* v_ctors_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_toConstantVal_1134_ = lean_ctor_get(v_indVal_1126_, 0);
lean_inc_ref(v_toConstantVal_1134_);
v_numParams_1135_ = lean_ctor_get(v_indVal_1126_, 1);
lean_inc(v_numParams_1135_);
v_ctors_1136_ = lean_ctor_get(v_indVal_1126_, 4);
lean_inc(v_ctors_1136_);
lean_dec_ref(v_indVal_1126_);
v___x_1137_ = lean_box(0);
v___x_1138_ = l_List_head_x21___redArg(v___x_1137_, v_ctors_1136_);
lean_dec(v_ctors_1136_);
v___x_1139_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v___x_1138_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v_toConstantVal_1142_; lean_object* v_env_1143_; lean_object* v_name_1144_; lean_object* v_targetNames_1145_; lean_object* v_type_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_st_ref_get(v_a_1132_);
v_toConstantVal_1142_ = lean_ctor_get(v_a_1140_, 0);
lean_inc_ref(v_toConstantVal_1142_);
lean_dec(v_a_1140_);
v_env_1143_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_env_1143_);
lean_dec(v___x_1141_);
v_name_1144_ = lean_ctor_get(v_toConstantVal_1134_, 0);
lean_inc(v_name_1144_);
lean_dec_ref(v_toConstantVal_1134_);
v_targetNames_1145_ = lean_ctor_get(v_header_1125_, 2);
v_type_1146_ = lean_ctor_get(v_toConstantVal_1142_, 2);
lean_inc_ref(v_type_1146_);
lean_dec_ref(v_toConstantVal_1142_);
v___x_1147_ = l_Lean_getStructureFields(v_env_1143_, v_name_1144_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_array_get_borrowed(v___x_1137_, v_targetNames_1145_, v___x_1148_);
lean_inc(v___x_1149_);
v___x_1150_ = l_Lean_mkIdent(v___x_1149_);
v___f_1151_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1151_, 0, v___x_1147_);
lean_closure_set(v___f_1151_, 1, v_numParams_1135_);
lean_closure_set(v___f_1151_, 2, v___x_1150_);
lean_closure_set(v___f_1151_, 3, v___x_1148_);
v___x_1152_ = 0;
v___x_1153_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_1146_, v___f_1151_, v___x_1152_, v___x_1152_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1153_;
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_numParams_1135_);
lean_dec_ref(v_toConstantVal_1134_);
v_a_1154_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1139_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1139_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object* v_header_1162_, lean_object* v_indVal_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_1162_, v_indVal_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_header_1162_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v_inst_1175_, lean_object* v_R_1176_, lean_object* v_a_1177_, lean_object* v_b_1178_, lean_object* v_c_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_1172_, v___x_1174_, v_a_1177_, v_b_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v___x_1183_, lean_object* v_inst_1184_, lean_object* v_R_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_, lean_object* v_c_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(v___x_1181_, v___x_1182_, v___x_1183_, v_inst_1184_, v_R_1185_, v_a_1186_, v_b_1187_, v_c_1188_);
lean_dec_ref(v___x_1183_);
lean_dec_ref(v___x_1182_);
lean_dec(v___x_1181_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object* v_upperBound_1190_, lean_object* v___x_1191_, lean_object* v___x_1192_, lean_object* v_xs_1193_, lean_object* v___x_1194_, lean_object* v_inst_1195_, lean_object* v_R_1196_, lean_object* v_a_1197_, lean_object* v_b_1198_, lean_object* v_c_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_1190_, v___x_1191_, v___x_1192_, v_xs_1193_, v___x_1194_, v_a_1197_, v_b_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_1208_ = _args[0];
lean_object* v___x_1209_ = _args[1];
lean_object* v___x_1210_ = _args[2];
lean_object* v_xs_1211_ = _args[3];
lean_object* v___x_1212_ = _args[4];
lean_object* v_inst_1213_ = _args[5];
lean_object* v_R_1214_ = _args[6];
lean_object* v_a_1215_ = _args[7];
lean_object* v_b_1216_ = _args[8];
lean_object* v_c_1217_ = _args[9];
lean_object* v___y_1218_ = _args[10];
lean_object* v___y_1219_ = _args[11];
lean_object* v___y_1220_ = _args[12];
lean_object* v___y_1221_ = _args[13];
lean_object* v___y_1222_ = _args[14];
lean_object* v___y_1223_ = _args[15];
lean_object* v___y_1224_ = _args[16];
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(v_upperBound_1208_, v___x_1209_, v___x_1210_, v_xs_1211_, v___x_1212_, v_inst_1213_, v_R_1214_, v_a_1215_, v_b_1216_, v_c_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v_xs_1211_);
lean_dec(v___x_1210_);
lean_dec_ref(v___x_1209_);
lean_dec(v_upperBound_1208_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object* v_00_u03b1_1226_, lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object* v_00_u03b1_1236_, lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(v_00_u03b1_1236_, v_msg_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(lean_object* v_msgData_1246_, lean_object* v_macroStack_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_1246_, v_macroStack_1247_, v___y_1252_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___boxed(lean_object* v_msgData_1256_, lean_object* v_macroStack_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(v_msgData_1256_, v_macroStack_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object* v_upperBound_1273_, lean_object* v_a_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_nat_dec_lt(v_a_1274_, v_upperBound_1273_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v_a_1274_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_b_1275_);
return v___x_1279_;
}
else
{
lean_object* v_ref_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_ref_1280_ = lean_ctor_get(v___y_1276_, 2);
v___x_1281_ = 0;
v___x_1282_ = l_Lean_SourceInfo_fromRef(v_ref_1280_, v___x_1281_);
v___x_1283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
lean_inc(v___x_1282_);
v___x_1285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1282_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_Syntax_node1(v___x_1282_, v___x_1283_, v___x_1285_);
v___x_1287_ = lean_array_push(v_b_1275_, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_a_1274_, v___x_1288_);
lean_dec(v_a_1274_);
v_a_1274_ = v___x_1289_;
v_b_1275_ = v___x_1287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_1291_, lean_object* v_a_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1291_, v_a_1292_, v_b_1293_, v___y_1294_);
lean_dec_ref(v___y_1294_);
lean_dec(v_upperBound_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t v_sz_1297_, size_t v_i_1298_, lean_object* v_bs_1299_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_usize_dec_lt(v_i_1298_, v_sz_1297_);
if (v___x_1300_ == 0)
{
return v_bs_1299_;
}
else
{
lean_object* v_v_1301_; lean_object* v___x_1302_; lean_object* v_bs_x27_1303_; size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v_v_1301_ = lean_array_uget(v_bs_1299_, v_i_1298_);
v___x_1302_ = lean_unsigned_to_nat(0u);
v_bs_x27_1303_ = lean_array_uset(v_bs_1299_, v_i_1298_, v___x_1302_);
v___x_1304_ = ((size_t)1ULL);
v___x_1305_ = lean_usize_add(v_i_1298_, v___x_1304_);
v___x_1306_ = lean_array_uset(v_bs_x27_1303_, v_i_1298_, v_v_1301_);
v_i_1298_ = v___x_1305_;
v_bs_1299_ = v___x_1306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_sz_1308_, lean_object* v_i_1309_, lean_object* v_bs_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1308_);
lean_dec(v_sz_1308_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_boxed_1311_, v_i_boxed_1312_, v_bs_1310_);
return v_res_1313_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0));
v___x_1316_ = l_String_toRawSubstring_x27(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object* v___f_1329_, lean_object* v_snd_1330_, lean_object* v___x_1331_, lean_object* v_toConstantVal_1332_, lean_object* v___x_1333_, lean_object* v_auxFunName_1334_, lean_object* v_____r_1335_, lean_object* v_ctorArgs_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = l_Lean_Expr_fvarId_x21(v___x_1331_);
v___x_1382_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_1381_, v___y_1339_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1510_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1510_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1510_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
uint8_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = lean_unbox(v_a_1383_);
lean_dec(v_a_1383_);
v___x_1388_ = l_Lean_BinderInfo_isExplicit(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec(v_auxFunName_1334_);
lean_dec(v___x_1333_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___f_1329_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_ctorArgs_1336_);
lean_ctor_set(v___x_1389_, 1, v_snd_1330_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1390_);
v___x_1392_ = v___x_1385_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
lean_object* v___x_1394_; 
lean_del_object(v___x_1385_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc_ref(v___x_1331_);
v___x_1394_ = lean_infer_type(v___x_1331_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_name_1396_; uint8_t v___x_1397_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v_name_1396_ = lean_ctor_get(v_toConstantVal_1332_, 0);
v___x_1397_ = l_Lean_Expr_isAppOf(v_a_1395_, v_name_1396_);
lean_dec(v_a_1395_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_dec(v_auxFunName_1334_);
lean_inc_ref(v___x_1331_);
v___x_1398_ = l_Lean_Meta_isType(v___x_1331_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; uint8_t v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = lean_unbox(v_a_1399_);
lean_dec(v_a_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Meta_isProof(v___x_1331_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; uint8_t v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = lean_unbox(v_a_1402_);
lean_dec(v_a_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1404_ = lean_apply_7(v___f_1329_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_toCold_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1436_; 
v_toCold_1405_ = lean_ctor_get(v___y_1341_, 0);
v_a_1406_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1408_ = v___x_1404_;
v_isShared_1409_ = v_isSharedCheck_1436_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1436_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_quotContext_1410_; lean_object* v_currMacroScope_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v_quotContext_1410_ = lean_ctor_get(v_toCold_1405_, 8);
v_currMacroScope_1411_ = lean_ctor_get(v_toCold_1405_, 9);
v___x_1412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_1413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_1406_, 6);
v___x_1414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_a_1406_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc_n(v_currMacroScope_1411_, 2);
lean_inc_n(v_quotContext_1410_, 2);
v___x_1417_ = l_Lean_addMacroScope(v_quotContext_1410_, v___x_1416_, v_currMacroScope_1411_);
v___x_1418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1406_);
lean_ctor_set(v___x_1419_, 1, v___x_1415_);
lean_ctor_set(v___x_1419_, 2, v___x_1417_);
lean_ctor_set(v___x_1419_, 3, v___x_1418_);
lean_inc_ref(v___x_1414_);
v___x_1420_ = l_Lean_Syntax_node3(v_a_1406_, v___x_1412_, v_snd_1330_, v___x_1414_, v___x_1419_);
v___x_1421_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32));
v___x_1422_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1);
v___x_1423_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2));
v___x_1424_ = l_Lean_addMacroScope(v_quotContext_1410_, v___x_1423_, v_currMacroScope_1411_);
v___x_1425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4));
v___x_1426_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1426_, 0, v_a_1406_);
lean_ctor_set(v___x_1426_, 1, v___x_1422_);
lean_ctor_set(v___x_1426_, 2, v___x_1424_);
lean_ctor_set(v___x_1426_, 3, v___x_1425_);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1428_ = l_Lean_Syntax_node1(v_a_1406_, v___x_1427_, v___x_1333_);
v___x_1429_ = l_Lean_Syntax_node2(v_a_1406_, v___x_1421_, v___x_1426_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_node3(v_a_1406_, v___x_1412_, v___x_1420_, v___x_1414_, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_ctorArgs_1336_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1432_);
v___x_1434_ = v___x_1408_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v___x_1333_);
lean_dec(v_snd_1330_);
v_a_1437_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1404_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1404_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_dec(v___x_1333_);
goto v___jp_1344_;
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v___x_1333_);
lean_dec(v_snd_1330_);
lean_dec_ref(v___f_1329_);
v_a_1445_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1401_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1401_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_dec(v___x_1333_);
lean_dec_ref(v___x_1331_);
goto v___jp_1344_;
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v___x_1333_);
lean_dec_ref(v___x_1331_);
lean_dec(v_snd_1330_);
lean_dec_ref(v___f_1329_);
v_a_1453_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1398_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1398_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v___x_1461_; 
lean_dec_ref(v___x_1331_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1461_ = lean_apply_7(v___f_1329_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_toCold_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1493_; 
v_toCold_1462_ = lean_ctor_get(v___y_1341_, 0);
v_a_1463_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1465_ = v___x_1461_;
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1461_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1493_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_quotContext_1467_; lean_object* v_currMacroScope_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v_quotContext_1467_ = lean_ctor_get(v_toCold_1462_, 8);
v_currMacroScope_1468_ = lean_ctor_get(v_toCold_1462_, 9);
v___x_1469_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_1470_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_1463_, 7);
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1463_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1473_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_1468_);
lean_inc(v_quotContext_1467_);
v___x_1474_ = l_Lean_addMacroScope(v_quotContext_1467_, v___x_1473_, v_currMacroScope_1468_);
v___x_1475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1476_, 0, v_a_1463_);
lean_ctor_set(v___x_1476_, 1, v___x_1472_);
lean_ctor_set(v___x_1476_, 2, v___x_1474_);
lean_ctor_set(v___x_1476_, 3, v___x_1475_);
lean_inc_ref(v___x_1471_);
v___x_1477_ = l_Lean_Syntax_node3(v_a_1463_, v___x_1469_, v_snd_1330_, v___x_1471_, v___x_1476_);
v___x_1478_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32));
v___x_1479_ = l_Lean_mkIdent(v_auxFunName_1334_);
v___x_1480_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1481_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1482_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_a_1463_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_Syntax_node1(v_a_1463_, v___x_1481_, v___x_1483_);
v___x_1485_ = l_Lean_Syntax_node2(v_a_1463_, v___x_1480_, v___x_1333_, v___x_1484_);
v___x_1486_ = l_Lean_Syntax_node2(v_a_1463_, v___x_1478_, v___x_1479_, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node3(v_a_1463_, v___x_1469_, v___x_1477_, v___x_1471_, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_ctorArgs_1336_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1489_);
v___x_1491_ = v___x_1465_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v_auxFunName_1334_);
lean_dec(v___x_1333_);
lean_dec(v_snd_1330_);
v_a_1494_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1461_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1461_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v_auxFunName_1334_);
lean_dec(v___x_1333_);
lean_dec_ref(v___x_1331_);
lean_dec(v_snd_1330_);
lean_dec_ref(v___f_1329_);
v_a_1502_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1394_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1394_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v_auxFunName_1334_);
lean_dec(v___x_1333_);
lean_dec_ref(v___x_1331_);
lean_dec(v_snd_1330_);
lean_dec_ref(v___f_1329_);
v_a_1511_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1382_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1382_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
v___jp_1344_:
{
lean_object* v___x_1345_; 
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1345_ = lean_apply_7(v___f_1329_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_toCold_1346_; lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1372_; 
v_toCold_1346_ = lean_ctor_get(v___y_1341_, 0);
v_a_1347_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1349_ = v___x_1345_;
v_isShared_1350_ = v_isSharedCheck_1372_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1372_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_quotContext_1351_; lean_object* v_currMacroScope_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v_quotContext_1351_ = lean_ctor_get(v_toCold_1346_, 8);
v_currMacroScope_1352_ = lean_ctor_get(v_toCold_1346_, 9);
v___x_1353_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_1354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_1347_, 5);
v___x_1355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1347_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1357_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_1352_);
lean_inc(v_quotContext_1351_);
v___x_1358_ = l_Lean_addMacroScope(v_quotContext_1351_, v___x_1357_, v_currMacroScope_1352_);
v___x_1359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1347_);
lean_ctor_set(v___x_1360_, 1, v___x_1356_);
lean_ctor_set(v___x_1360_, 2, v___x_1358_);
lean_ctor_set(v___x_1360_, 3, v___x_1359_);
lean_inc_ref(v___x_1355_);
v___x_1361_ = l_Lean_Syntax_node3(v_a_1347_, v___x_1353_, v_snd_1330_, v___x_1355_, v___x_1360_);
v___x_1362_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_1363_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_1364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1347_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_Syntax_node1(v_a_1347_, v___x_1362_, v___x_1364_);
v___x_1366_ = l_Lean_Syntax_node3(v_a_1347_, v___x_1353_, v___x_1361_, v___x_1355_, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_ctorArgs_1336_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1368_);
v___x_1370_ = v___x_1349_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_ctorArgs_1336_);
lean_dec(v_snd_1330_);
v_a_1373_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1345_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1345_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object* v___f_1519_, lean_object* v_snd_1520_, lean_object* v___x_1521_, lean_object* v_toConstantVal_1522_, lean_object* v___x_1523_, lean_object* v_auxFunName_1524_, lean_object* v_____r_1525_, lean_object* v_ctorArgs_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1519_, v_snd_1520_, v___x_1521_, v_toConstantVal_1522_, v___x_1523_, v_auxFunName_1524_, v_____r_1525_, v_ctorArgs_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v_toConstantVal_1522_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object* v_upperBound_1538_, lean_object* v_xs_1539_, lean_object* v_indVal_1540_, lean_object* v_auxFunName_1541_, lean_object* v_header_1542_, lean_object* v_a_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___y_1553_; uint8_t v___x_1575_; 
v___x_1575_ = lean_nat_dec_lt(v_a_1543_, v_upperBound_1538_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_a_1543_);
lean_dec(v_auxFunName_1541_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_b_1544_);
return v___x_1576_;
}
else
{
lean_object* v_fst_1577_; lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1626_; 
v_fst_1577_ = lean_ctor_get(v_b_1544_, 0);
v_snd_1578_ = lean_ctor_get(v_b_1544_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_b_1544_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1580_ = v_b_1544_;
v_isShared_1581_ = v_isSharedCheck_1626_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_inc(v_fst_1577_);
lean_dec(v_b_1544_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1626_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_toConstantVal_1582_; lean_object* v_numParams_1583_; lean_object* v___f_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v_a_1588_; 
v_toConstantVal_1582_ = lean_ctor_get(v_indVal_1540_, 0);
v_numParams_1583_ = lean_ctor_get(v_indVal_1540_, 1);
v___f_1584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0));
v___x_1585_ = lean_array_fget_borrowed(v_xs_1539_, v_a_1543_);
v___x_1586_ = lean_nat_dec_lt(v_a_1543_, v_numParams_1583_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1));
v___x_1613_ = l_Lean_Core_mkFreshUserName(v___x_1612_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v_a_1588_ = v_a_1614_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1580_);
lean_dec(v_snd_1578_);
lean_dec(v_fst_1577_);
lean_dec(v_a_1543_);
lean_dec(v_auxFunName_1541_);
v_a_1615_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1613_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1613_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_argNames_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_argNames_1623_ = lean_ctor_get(v_header_1542_, 1);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_array_get_borrowed(v___x_1624_, v_argNames_1623_, v_a_1543_);
lean_inc(v___x_1625_);
v_a_1588_ = v___x_1625_;
goto v___jp_1587_;
}
v___jp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_mkIdent(v_a_1588_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_del_object(v___x_1580_);
lean_inc(v___x_1589_);
v___x_1590_ = lean_array_push(v_fst_1577_, v___x_1589_);
v___x_1591_ = lean_box(0);
lean_inc(v_auxFunName_1541_);
lean_inc(v___x_1585_);
v___x_1592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1584_, v_snd_1578_, v___x_1585_, v_toConstantVal_1582_, v___x_1589_, v_auxFunName_1541_, v___x_1591_, v___x_1590_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
v___y_1553_ = v___x_1592_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_n(v_a_1594_, 2);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1596_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 2);
lean_ctor_set(v___x_1580_, 1, v___x_1596_);
lean_ctor_set(v___x_1580_, 0, v_a_1594_);
v___x_1598_ = v___x_1580_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1594_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1599_ = l_Lean_Syntax_node1(v_a_1594_, v___x_1595_, v___x_1598_);
v___x_1600_ = lean_array_push(v_fst_1577_, v___x_1599_);
v___x_1601_ = lean_box(0);
lean_inc(v_auxFunName_1541_);
lean_inc(v___x_1585_);
v___x_1602_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1584_, v_snd_1578_, v___x_1585_, v_toConstantVal_1582_, v___x_1589_, v_auxFunName_1541_, v___x_1601_, v___x_1600_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
v___y_1553_ = v___x_1602_;
goto v___jp_1552_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v___x_1589_);
lean_del_object(v___x_1580_);
lean_dec(v_snd_1578_);
lean_dec(v_fst_1577_);
lean_dec(v_a_1543_);
lean_dec(v_auxFunName_1541_);
v_a_1604_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1593_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1593_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
}
v___jp_1552_:
{
if (lean_obj_tag(v___y_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1566_; 
v_a_1554_ = lean_ctor_get(v___y_1553_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___y_1553_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1556_ = v___y_1553_;
v_isShared_1557_ = v_isSharedCheck_1566_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___y_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1566_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
if (lean_obj_tag(v_a_1554_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; 
lean_dec(v_a_1543_);
lean_dec(v_auxFunName_1541_);
v_a_1558_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v_a_1554_, 1);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v_a_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1558_);
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
lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_del_object(v___x_1556_);
v_a_1562_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v_a_1554_, 1);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_add(v_a_1543_, v___x_1563_);
lean_dec(v_a_1543_);
v_a_1543_ = v___x_1564_;
v_b_1544_ = v_a_1562_;
goto _start;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1543_);
lean_dec(v_auxFunName_1541_);
v_a_1567_ = lean_ctor_get(v___y_1553_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___y_1553_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___y_1553_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___y_1553_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1627_, lean_object* v_xs_1628_, lean_object* v_indVal_1629_, lean_object* v_auxFunName_1630_, lean_object* v_header_1631_, lean_object* v_a_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_1627_, v_xs_1628_, v_indVal_1629_, v_auxFunName_1630_, v_header_1631_, v_a_1632_, v_b_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec_ref(v_header_1631_);
lean_dec_ref(v_indVal_1629_);
lean_dec_ref(v_xs_1628_);
lean_dec(v_upperBound_1627_);
return v_res_1641_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4));
v___x_1655_ = l_String_toRawSubstring_x27(v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15));
v___x_1680_ = l_Lean_mkAtom(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18));
v___x_1684_ = l_String_toRawSubstring_x27(v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object* v_indVal_1740_, lean_object* v___x_1741_, lean_object* v_alts_1742_, lean_object* v_name_1743_, lean_object* v_auxFunName_1744_, lean_object* v_header_1745_, lean_object* v___f_1746_, lean_object* v_head_1747_, lean_object* v_xs_1748_, lean_object* v_x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_numIndices_1757_; lean_object* v___x_1758_; 
v_numIndices_1757_ = lean_ctor_get(v_indVal_1740_, 2);
lean_inc_ref(v_alts_1742_);
lean_inc(v___x_1741_);
v___x_1758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_numIndices_1757_, v___x_1741_, v_alts_1742_, v___y_1754_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_toCold_1759_; lean_object* v_a_1760_; lean_object* v_ref_1761_; lean_object* v_quotContext_1762_; lean_object* v_currMacroScope_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_toCold_1759_ = lean_ctor_get(v___y_1754_, 0);
v_a_1760_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1758_, 1);
v_ref_1761_ = lean_ctor_get(v___y_1754_, 2);
v_quotContext_1762_ = lean_ctor_get(v_toCold_1759_, 8);
v_currMacroScope_1763_ = lean_ctor_get(v_toCold_1759_, 9);
v___x_1764_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1));
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_array_get_size(v_xs_1748_);
v___x_1767_ = 0;
v___x_1768_ = l_Lean_SourceInfo_fromRef(v_ref_1761_, v___x_1767_);
v___x_1769_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5);
lean_inc(v_currMacroScope_1763_);
lean_inc(v_quotContext_1762_);
v___x_1770_ = l_Lean_addMacroScope(v_quotContext_1762_, v___x_1764_, v_currMacroScope_1763_);
v___x_1771_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8));
lean_inc_n(v___x_1768_, 2);
v___x_1772_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1768_);
lean_ctor_set(v___x_1772_, 1, v___x_1769_);
lean_ctor_set(v___x_1772_, 2, v___x_1770_);
lean_ctor_set(v___x_1772_, 3, v___x_1771_);
v___x_1773_ = 1;
v___x_1774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1743_, v___x_1773_);
v___x_1775_ = lean_box(2);
v___x_1776_ = l_Lean_Syntax_mkStrLit(v___x_1774_, v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1778_ = l_Lean_Syntax_node1(v___x_1768_, v___x_1777_, v___x_1776_);
v___x_1779_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32));
v___x_1780_ = l_Lean_Syntax_node2(v___x_1768_, v___x_1779_, v___x_1772_, v___x_1778_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_alts_1742_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v___x_1766_, v_xs_1748_, v_indVal_1740_, v_auxFunName_1744_, v_header_1745_, v___x_1741_, v___x_1781_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v_fst_1784_; lean_object* v_snd_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1908_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v_fst_1784_ = lean_ctor_get(v_a_1783_, 0);
v_snd_1785_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1787_ = v_a_1783_;
v_isShared_1788_ = v_isSharedCheck_1908_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_snd_1785_);
lean_inc(v_fst_1784_);
lean_dec(v_a_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1908_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; 
lean_inc_ref(v___f_1746_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1752_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
v___x_1789_ = lean_apply_7(v___f_1746_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, lean_box(0));
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc_n(v_a_1790_, 2);
lean_dec_ref_known(v___x_1789_, 1);
v___x_1791_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10));
v___x_1792_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11));
if (v_isShared_1788_ == 0)
{
lean_ctor_set_tag(v___x_1787_, 2);
lean_ctor_set(v___x_1787_, 1, v___x_1792_);
lean_ctor_set(v___x_1787_, 0, v_a_1790_);
v___x_1794_ = v___x_1787_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1790_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1795_ = l_Lean_mkIdent(v_head_1747_);
lean_inc_n(v_a_1790_, 2);
v___x_1796_ = l_Lean_Syntax_node2(v_a_1790_, v___x_1791_, v___x_1794_, v___x_1795_);
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_1798_ = l_Array_append___redArg(v___x_1797_, v_fst_1784_);
lean_dec(v_fst_1784_);
v___x_1799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1799_, 0, v_a_1790_);
lean_ctor_set(v___x_1799_, 1, v___x_1777_);
lean_ctor_set(v___x_1799_, 2, v___x_1798_);
v___x_1800_ = l_Lean_Syntax_node2(v_a_1790_, v___x_1779_, v___x_1796_, v___x_1799_);
v___x_1801_ = lean_array_push(v_a_1760_, v___x_1800_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1752_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
v___x_1802_ = lean_apply_7(v___f_1746_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1890_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1890_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1890_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; size_t v_sz_1810_; size_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13));
v___x_1808_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14));
lean_inc_n(v_a_1803_, 35);
v___x_1809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_a_1803_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v_sz_1810_ = lean_array_size(v___x_1801_);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_1810_, v___x_1811_, v___x_1801_);
v___x_1813_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_1814_ = l_Lean_mkSepArray(v___x_1812_, v___x_1813_);
lean_dec_ref(v___x_1812_);
v___x_1815_ = l_Array_append___redArg(v___x_1797_, v___x_1814_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1816_, 0, v_a_1803_);
lean_ctor_set(v___x_1816_, 1, v___x_1777_);
lean_ctor_set(v___x_1816_, 2, v___x_1815_);
v___x_1817_ = l_Lean_Syntax_node1(v_a_1803_, v___x_1777_, v___x_1816_);
v___x_1818_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17));
v___x_1819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1803_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19);
v___x_1821_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21));
lean_inc_n(v_currMacroScope_1763_, 5);
lean_inc_n(v_quotContext_1762_, 5);
v___x_1822_ = l_Lean_addMacroScope(v_quotContext_1762_, v___x_1821_, v_currMacroScope_1763_);
v___x_1823_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23));
v___x_1824_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1803_);
lean_ctor_set(v___x_1824_, 1, v___x_1820_);
lean_ctor_set(v___x_1824_, 2, v___x_1822_);
lean_ctor_set(v___x_1824_, 3, v___x_1823_);
v___x_1825_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8));
v___x_1826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10));
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_1828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1803_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12));
v___x_1830_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14);
v___x_1831_ = lean_box(0);
v___x_1832_ = l_Lean_addMacroScope(v_quotContext_1762_, v___x_1831_, v_currMacroScope_1763_);
v___x_1833_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27));
v___x_1834_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1834_, 0, v_a_1803_);
lean_ctor_set(v___x_1834_, 1, v___x_1830_);
lean_ctor_set(v___x_1834_, 2, v___x_1832_);
lean_ctor_set(v___x_1834_, 3, v___x_1833_);
v___x_1835_ = l_Lean_Syntax_node1(v_a_1803_, v___x_1829_, v___x_1834_);
v___x_1836_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1826_, v___x_1828_, v___x_1835_);
v___x_1837_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34);
v___x_1838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37));
v___x_1839_ = l_Lean_addMacroScope(v_quotContext_1762_, v___x_1838_, v_currMacroScope_1763_);
v___x_1840_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30));
v___x_1841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1803_);
lean_ctor_set(v___x_1841_, 1, v___x_1837_);
lean_ctor_set(v___x_1841_, 2, v___x_1839_);
lean_ctor_set(v___x_1841_, 3, v___x_1840_);
v___x_1842_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44);
v___x_1843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46));
v___x_1844_ = l_Lean_addMacroScope(v_quotContext_1762_, v___x_1843_, v_currMacroScope_1763_);
v___x_1845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33));
v___x_1846_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1846_, 0, v_a_1803_);
lean_ctor_set(v___x_1846_, 1, v___x_1842_);
lean_ctor_set(v___x_1846_, 2, v___x_1844_);
lean_ctor_set(v___x_1846_, 3, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35));
v___x_1848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1803_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38));
v___x_1851_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
v___x_1853_ = l_Lean_addMacroScope(v_quotContext_1762_, v___x_1852_, v_currMacroScope_1763_);
v___x_1854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1803_);
lean_ctor_set(v___x_1854_, 1, v___x_1851_);
lean_ctor_set(v___x_1854_, 2, v___x_1853_);
lean_ctor_set(v___x_1854_, 3, v___x_1765_);
v___x_1855_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39));
v___x_1856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_a_1803_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1858_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1803_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_Syntax_node1(v_a_1803_, v___x_1857_, v___x_1859_);
lean_inc_ref(v___x_1854_);
v___x_1861_ = l_Lean_Syntax_node3(v_a_1803_, v___x_1850_, v___x_1854_, v___x_1856_, v___x_1860_);
v___x_1862_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40));
v___x_1863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_a_1803_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42));
v___x_1865_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43));
v___x_1866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1866_, 0, v_a_1803_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_Syntax_node1(v_a_1803_, v___x_1864_, v___x_1866_);
v___x_1868_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44));
v___x_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1803_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45));
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1803_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_Syntax_node1(v_a_1803_, v___x_1864_, v___x_1871_);
v___x_1873_ = l_Lean_Syntax_node6(v_a_1803_, v___x_1847_, v___x_1849_, v___x_1861_, v___x_1863_, v___x_1867_, v___x_1869_, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_1875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1803_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_inc_ref_n(v___x_1875_, 3);
lean_inc_n(v___x_1836_, 3);
v___x_1876_ = l_Lean_Syntax_node3(v_a_1803_, v___x_1825_, v___x_1836_, v___x_1873_, v___x_1875_);
v___x_1877_ = l_Lean_Syntax_node3(v_a_1803_, v___x_1825_, v___x_1836_, v_snd_1785_, v___x_1875_);
v___x_1878_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1777_, v___x_1876_, v___x_1877_);
v___x_1879_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1779_, v___x_1846_, v___x_1878_);
v___x_1880_ = l_Lean_Syntax_node3(v_a_1803_, v___x_1825_, v___x_1836_, v___x_1879_, v___x_1875_);
v___x_1881_ = l_Lean_Syntax_node1(v_a_1803_, v___x_1777_, v___x_1880_);
v___x_1882_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1779_, v___x_1841_, v___x_1881_);
v___x_1883_ = l_Lean_Syntax_node3(v_a_1803_, v___x_1825_, v___x_1836_, v___x_1882_, v___x_1875_);
v___x_1884_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1777_, v___x_1883_, v___x_1854_);
v___x_1885_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1779_, v___x_1824_, v___x_1884_);
v___x_1886_ = l_Lean_Syntax_node4(v_a_1803_, v___x_1807_, v___x_1809_, v___x_1817_, v___x_1819_, v___x_1885_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1886_);
v___x_1888_ = v___x_1805_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v___x_1801_);
lean_dec(v_snd_1785_);
v_a_1891_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1802_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1802_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_del_object(v___x_1787_);
lean_dec(v_snd_1785_);
lean_dec(v_fst_1784_);
lean_dec(v_a_1760_);
lean_dec(v_head_1747_);
lean_dec_ref(v___f_1746_);
v_a_1900_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1789_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1789_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1760_);
lean_dec(v_head_1747_);
lean_dec_ref(v___f_1746_);
v_a_1909_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1782_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1782_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_head_1747_);
lean_dec_ref(v___f_1746_);
lean_dec(v_auxFunName_1744_);
lean_dec(v_name_1743_);
lean_dec_ref(v_alts_1742_);
lean_dec(v___x_1741_);
v_a_1917_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1758_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1758_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1925_ = _args[0];
lean_object* v___x_1926_ = _args[1];
lean_object* v_alts_1927_ = _args[2];
lean_object* v_name_1928_ = _args[3];
lean_object* v_auxFunName_1929_ = _args[4];
lean_object* v_header_1930_ = _args[5];
lean_object* v___f_1931_ = _args[6];
lean_object* v_head_1932_ = _args[7];
lean_object* v_xs_1933_ = _args[8];
lean_object* v_x_1934_ = _args[9];
lean_object* v___y_1935_ = _args[10];
lean_object* v___y_1936_ = _args[11];
lean_object* v___y_1937_ = _args[12];
lean_object* v___y_1938_ = _args[13];
lean_object* v___y_1939_ = _args[14];
lean_object* v___y_1940_ = _args[15];
lean_object* v___y_1941_ = _args[16];
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(v_indVal_1925_, v___x_1926_, v_alts_1927_, v_name_1928_, v_auxFunName_1929_, v_header_1930_, v___f_1931_, v_head_1932_, v_xs_1933_, v_x_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec_ref(v_x_1934_);
lean_dec_ref(v_xs_1933_);
lean_dec_ref(v_header_1930_);
lean_dec_ref(v_indVal_1925_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_ref_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_ref_1950_ = lean_ctor_get(v___y_1947_, 2);
v___x_1951_ = 0;
v___x_1952_ = l_Lean_SourceInfo_fromRef(v_ref_1950_, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object* v_indVal_1965_, lean_object* v_auxFunName_1966_, lean_object* v_header_1967_, lean_object* v_as_x27_1968_, lean_object* v_b_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
if (lean_obj_tag(v_as_x27_1968_) == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref(v_header_1967_);
lean_dec(v_auxFunName_1966_);
lean_dec_ref(v_indVal_1965_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_b_1969_);
return v___x_1977_;
}
else
{
lean_object* v_head_1978_; lean_object* v_tail_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; lean_object* v_alts_1982_; lean_object* v___x_1983_; 
v_head_1978_ = lean_ctor_get(v_as_x27_1968_, 0);
v_tail_1979_ = lean_ctor_get(v_as_x27_1968_, 1);
v___f_1980_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0));
v___x_1981_ = lean_unsigned_to_nat(0u);
v_alts_1982_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
lean_inc(v_head_1978_);
v___x_1983_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_head_1978_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v_toConstantVal_1985_; lean_object* v_name_1986_; lean_object* v_type_1987_; lean_object* v___f_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v_toConstantVal_1985_ = lean_ctor_get(v_a_1984_, 0);
lean_inc_ref(v_toConstantVal_1985_);
lean_dec(v_a_1984_);
v_name_1986_ = lean_ctor_get(v_toConstantVal_1985_, 0);
lean_inc(v_name_1986_);
v_type_1987_ = lean_ctor_get(v_toConstantVal_1985_, 2);
lean_inc_ref(v_type_1987_);
lean_dec_ref(v_toConstantVal_1985_);
lean_inc(v_head_1978_);
lean_inc_ref(v_header_1967_);
lean_inc(v_auxFunName_1966_);
lean_inc_ref(v_indVal_1965_);
v___f_1988_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1988_, 0, v_indVal_1965_);
lean_closure_set(v___f_1988_, 1, v___x_1981_);
lean_closure_set(v___f_1988_, 2, v_alts_1982_);
lean_closure_set(v___f_1988_, 3, v_name_1986_);
lean_closure_set(v___f_1988_, 4, v_auxFunName_1966_);
lean_closure_set(v___f_1988_, 5, v_header_1967_);
lean_closure_set(v___f_1988_, 6, v___f_1980_);
lean_closure_set(v___f_1988_, 7, v_head_1978_);
v___x_1989_ = 0;
v___x_1990_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_1987_, v___f_1988_, v___x_1989_, v___x_1989_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_array_push(v_b_1969_, v_a_1991_);
v_as_x27_1968_ = v_tail_1979_;
v_b_1969_ = v___x_1992_;
goto _start;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_header_1967_);
lean_dec(v_auxFunName_1966_);
lean_dec_ref(v_indVal_1965_);
v_a_1994_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1990_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1990_);
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
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_header_1967_);
lean_dec(v_auxFunName_1966_);
lean_dec_ref(v_indVal_1965_);
v_a_2002_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1983_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1983_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object* v_indVal_2010_, lean_object* v_auxFunName_2011_, lean_object* v_header_2012_, lean_object* v_as_x27_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2010_, v_auxFunName_2011_, v_header_2012_, v_as_x27_2013_, v_b_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v_as_x27_2013_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t v_sz_2023_, size_t v_i_2024_, lean_object* v_bs_2025_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
if (v___x_2026_ == 0)
{
return v_bs_2025_;
}
else
{
lean_object* v_v_2027_; lean_object* v___x_2028_; lean_object* v_bs_x27_2029_; size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v_v_2027_ = lean_array_uget(v_bs_2025_, v_i_2024_);
v___x_2028_ = lean_unsigned_to_nat(0u);
v_bs_x27_2029_ = lean_array_uset(v_bs_2025_, v_i_2024_, v___x_2028_);
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2024_, v___x_2030_);
v___x_2032_ = lean_array_uset(v_bs_x27_2029_, v_i_2024_, v_v_2027_);
v_i_2024_ = v___x_2031_;
v_bs_2025_ = v___x_2032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_sz_2034_, lean_object* v_i_2035_, lean_object* v_bs_2036_){
_start:
{
size_t v_sz_boxed_2037_; size_t v_i_boxed_2038_; lean_object* v_res_2039_; 
v_sz_boxed_2037_ = lean_unbox_usize(v_sz_2034_);
lean_dec(v_sz_2034_);
v_i_boxed_2038_ = lean_unbox_usize(v_i_2035_);
lean_dec(v_i_2035_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_boxed_2037_, v_i_boxed_2038_, v_bs_2036_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object* v_header_2040_, lean_object* v_indVal_2041_, lean_object* v_auxFunName_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_ctors_2050_; lean_object* v_alts_2051_; lean_object* v___x_2052_; 
v_ctors_2050_ = lean_ctor_get(v_indVal_2041_, 4);
lean_inc(v_ctors_2050_);
v_alts_2051_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2052_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2041_, v_auxFunName_2042_, v_header_2040_, v_ctors_2050_, v_alts_2051_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_ctors_2050_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2063_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
size_t v_sz_2057_; size_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
v_sz_2057_ = lean_array_size(v_a_2053_);
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_2057_, v___x_2058_, v_a_2053_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2059_);
v___x_2061_ = v___x_2055_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object* v_header_2064_, lean_object* v_indVal_2065_, lean_object* v_auxFunName_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2064_, v_indVal_2065_, v_auxFunName_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object* v_upperBound_2075_, lean_object* v_xs_2076_, lean_object* v_indVal_2077_, lean_object* v_auxFunName_2078_, lean_object* v_header_2079_, lean_object* v_inst_2080_, lean_object* v_R_2081_, lean_object* v_a_2082_, lean_object* v_b_2083_, lean_object* v_c_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_2075_, v_xs_2076_, v_indVal_2077_, v_auxFunName_2078_, v_header_2079_, v_a_2082_, v_b_2083_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2093_ = _args[0];
lean_object* v_xs_2094_ = _args[1];
lean_object* v_indVal_2095_ = _args[2];
lean_object* v_auxFunName_2096_ = _args[3];
lean_object* v_header_2097_ = _args[4];
lean_object* v_inst_2098_ = _args[5];
lean_object* v_R_2099_ = _args[6];
lean_object* v_a_2100_ = _args[7];
lean_object* v_b_2101_ = _args[8];
lean_object* v_c_2102_ = _args[9];
lean_object* v___y_2103_ = _args[10];
lean_object* v___y_2104_ = _args[11];
lean_object* v___y_2105_ = _args[12];
lean_object* v___y_2106_ = _args[13];
lean_object* v___y_2107_ = _args[14];
lean_object* v___y_2108_ = _args[15];
lean_object* v___y_2109_ = _args[16];
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(v_upperBound_2093_, v_xs_2094_, v_indVal_2095_, v_auxFunName_2096_, v_header_2097_, v_inst_2098_, v_R_2099_, v_a_2100_, v_b_2101_, v_c_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v_header_2097_);
lean_dec_ref(v_indVal_2095_);
lean_dec_ref(v_xs_2094_);
lean_dec(v_upperBound_2093_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object* v_upperBound_2111_, lean_object* v_inst_2112_, lean_object* v_R_2113_, lean_object* v_a_2114_, lean_object* v_b_2115_, lean_object* v_c_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_2111_, v_a_2114_, v_b_2115_, v___y_2121_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object* v_upperBound_2125_, lean_object* v_inst_2126_, lean_object* v_R_2127_, lean_object* v_a_2128_, lean_object* v_b_2129_, lean_object* v_c_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(v_upperBound_2125_, v_inst_2126_, v_R_2127_, v_a_2128_, v_b_2129_, v_c_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v_upperBound_2125_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object* v_indVal_2139_, lean_object* v_auxFunName_2140_, lean_object* v_header_2141_, lean_object* v_as_2142_, lean_object* v_as_x27_2143_, lean_object* v_b_2144_, lean_object* v_a_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2139_, v_auxFunName_2140_, v_header_2141_, v_as_x27_2143_, v_b_2144_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_indVal_2154_, lean_object* v_auxFunName_2155_, lean_object* v_header_2156_, lean_object* v_as_2157_, lean_object* v_as_x27_2158_, lean_object* v_b_2159_, lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(v_indVal_2154_, v_auxFunName_2155_, v_header_2156_, v_as_2157_, v_as_x27_2158_, v_b_2159_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v_as_x27_2158_);
lean_dec(v_as_2157_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object* v_header_2182_, lean_object* v_indVal_2183_, lean_object* v_auxFunName_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; 
lean_inc_ref(v_indVal_2183_);
lean_inc_ref(v_header_2182_);
v___x_2192_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2182_, v_indVal_2183_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2182_, v_indVal_2183_, v_auxFunName_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2225_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2225_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2225_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_ref_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; size_t v_sz_2208_; size_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v_ref_2199_ = lean_ctor_get(v_a_2189_, 2);
v___x_2200_ = 0;
v___x_2201_ = l_Lean_SourceInfo_fromRef(v_ref_2199_, v___x_2200_);
v___x_2202_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0));
v___x_2203_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1));
lean_inc_n(v___x_2201_, 6);
v___x_2204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2201_);
lean_ctor_set(v___x_2204_, 1, v___x_2202_);
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2206_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2201_);
lean_ctor_set(v___x_2207_, 1, v___x_2205_);
lean_ctor_set(v___x_2207_, 2, v___x_2206_);
v_sz_2208_ = lean_array_size(v_a_2193_);
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_2208_, v___x_2209_, v_a_2193_);
v___x_2211_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_2212_ = l_Lean_mkSepArray(v___x_2210_, v___x_2211_);
lean_dec_ref(v___x_2210_);
v___x_2213_ = l_Array_append___redArg(v___x_2206_, v___x_2212_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2201_);
lean_ctor_set(v___x_2214_, 1, v___x_2205_);
lean_ctor_set(v___x_2214_, 2, v___x_2213_);
v___x_2215_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2));
v___x_2216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2201_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4));
v___x_2218_ = l_Array_append___redArg(v___x_2206_, v_a_2195_);
lean_dec(v_a_2195_);
v___x_2219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2201_);
lean_ctor_set(v___x_2219_, 1, v___x_2205_);
lean_ctor_set(v___x_2219_, 2, v___x_2218_);
v___x_2220_ = l_Lean_Syntax_node1(v___x_2201_, v___x_2217_, v___x_2219_);
lean_inc_ref(v___x_2207_);
v___x_2221_ = l_Lean_Syntax_node6(v___x_2201_, v___x_2203_, v___x_2204_, v___x_2207_, v___x_2207_, v___x_2214_, v___x_2216_, v___x_2220_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2221_);
v___x_2223_ = v___x_2197_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2193_);
v_a_2226_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2194_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2194_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_auxFunName_2184_);
lean_dec_ref(v_indVal_2183_);
lean_dec_ref(v_header_2182_);
v_a_2234_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2192_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2192_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object* v_header_2242_, lean_object* v_indVal_2243_, lean_object* v_auxFunName_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2242_, v_indVal_2243_, v_auxFunName_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object* v_header_2253_, lean_object* v_indVal_2254_, lean_object* v_auxFunName_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v_toConstantVal_2264_; lean_object* v_env_2265_; lean_object* v_name_2266_; uint8_t v___x_2267_; 
v___x_2263_ = lean_st_ref_get(v_a_2261_);
v_toConstantVal_2264_ = lean_ctor_get(v_indVal_2254_, 0);
v_env_2265_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_env_2265_);
lean_dec(v___x_2263_);
v_name_2266_ = lean_ctor_get(v_toConstantVal_2264_, 0);
lean_inc(v_name_2266_);
v___x_2267_ = l_Lean_isStructure(v_env_2265_, v_name_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2253_, v_indVal_2254_, v_auxFunName_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; 
lean_dec(v_auxFunName_2255_);
v___x_2269_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_2253_, v_indVal_2254_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_header_2253_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object* v_header_2270_, lean_object* v_indVal_2271_, lean_object* v_auxFunName_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Elab_Deriving_Repr_mkBody(v_header_2270_, v_indVal_2271_, v_auxFunName_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2280_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15));
v___x_2322_ = l_String_toRawSubstring_x27(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35));
v___x_2352_ = l_String_toRawSubstring_x27(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object* v_ctx_2389_, lean_object* v_i_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_typeInfos_2398_; lean_object* v_auxFunNames_2399_; uint8_t v_usePartial_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v_auxFunName_2403_; lean_object* v_indVal_2404_; lean_object* v___x_2405_; 
v_typeInfos_2398_ = lean_ctor_get(v_ctx_2389_, 1);
v_auxFunNames_2399_ = lean_ctor_get(v_ctx_2389_, 2);
v_usePartial_2400_ = lean_ctor_get_uint8(v_ctx_2389_, sizeof(void*)*3);
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_2403_ = lean_array_get_borrowed(v___x_2401_, v_auxFunNames_2399_, v_i_2390_);
v_indVal_2404_ = lean_array_get_borrowed(v___x_2402_, v_typeInfos_2398_, v_i_2390_);
lean_inc(v_indVal_2404_);
v___x_2405_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_2404_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2578_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2578_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2578_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_body_2411_; lean_object* v___y_2412_; lean_object* v___x_2561_; 
lean_inc(v_auxFunName_2403_);
lean_inc(v_indVal_2404_);
lean_inc(v_a_2406_);
v___x_2561_ = l_Lean_Elab_Deriving_Repr_mkBody(v_a_2406_, v_indVal_2404_, v_auxFunName_2403_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2561_) == 0)
{
if (v_usePartial_2400_ == 0)
{
lean_object* v_a_2562_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v_body_2411_ = v_a_2562_;
v___y_2412_ = v_a_2395_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2563_; lean_object* v_argNames_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_a_2563_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2561_, 1);
v_argNames_2564_ = lean_ctor_get(v_a_2406_, 1);
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
lean_inc_ref(v_argNames_2564_);
v___x_2566_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2389_, v___x_2565_, v_argNames_2564_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = l_Lean_Elab_Deriving_mkLet(v_a_2567_, v_a_2563_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v_body_2411_ = v_a_2569_;
v___y_2412_ = v_a_2395_;
goto v___jp_2410_;
}
else
{
lean_del_object(v___x_2408_);
lean_dec(v_a_2406_);
return v___x_2568_;
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_a_2563_);
lean_del_object(v___x_2408_);
lean_dec(v_a_2406_);
v_a_2570_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2566_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2566_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_del_object(v___x_2408_);
lean_dec(v_a_2406_);
return v___x_2561_;
}
v___jp_2410_:
{
if (v_usePartial_2400_ == 0)
{
lean_object* v_toCold_2413_; lean_object* v_binders_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2480_; 
v_toCold_2413_ = lean_ctor_get(v___y_2412_, 0);
v_binders_2414_ = lean_ctor_get(v_a_2406_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; 
v_unused_2481_ = lean_ctor_get(v_a_2406_, 3);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_a_2406_, 2);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_a_2406_, 1);
lean_dec(v_unused_2483_);
v___x_2416_ = v_a_2406_;
v_isShared_2417_ = v_isSharedCheck_2480_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_binders_2414_);
lean_dec(v_a_2406_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2480_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_ref_2418_; lean_object* v_quotContext_2419_; lean_object* v_currMacroScope_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v_ref_2418_ = lean_ctor_get(v___y_2412_, 2);
v_quotContext_2419_ = lean_ctor_get(v_toCold_2413_, 8);
v_currMacroScope_2420_ = lean_ctor_get(v_toCold_2413_, 9);
v___x_2421_ = l_Lean_SourceInfo_fromRef(v_ref_2418_, v_usePartial_2400_);
v___x_2422_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2424_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2425_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2421_, 4);
v___x_2426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2421_);
lean_ctor_set(v___x_2426_, 1, v___x_2424_);
lean_ctor_set(v___x_2426_, 2, v___x_2425_);
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2428_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2421_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2426_);
v___x_2432_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2431_, v___x_2426_);
v___x_2433_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2434_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2420_);
lean_inc(v_quotContext_2419_);
v___x_2436_ = l_Lean_addMacroScope(v_quotContext_2419_, v___x_2435_, v_currMacroScope_2420_);
v___x_2437_ = lean_box(0);
if (v_isShared_2417_ == 0)
{
lean_ctor_set_tag(v___x_2416_, 3);
lean_ctor_set(v___x_2416_, 3, v___x_2437_);
lean_ctor_set(v___x_2416_, 2, v___x_2436_);
lean_ctor_set(v___x_2416_, 1, v___x_2434_);
lean_ctor_set(v___x_2416_, 0, v___x_2421_);
v___x_2439_ = v___x_2416_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_inc_ref_n(v___x_2426_, 11);
lean_inc_n(v___x_2421_, 19);
v___x_2440_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2433_, v___x_2439_, v___x_2426_);
v___x_2441_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2430_, v___x_2432_, v___x_2440_);
v___x_2442_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2424_, v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2421_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = l_Lean_Syntax_node3(v___x_2421_, v___x_2427_, v___x_2429_, v___x_2442_, v___x_2444_);
v___x_2446_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2424_, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node7(v___x_2421_, v___x_2423_, v___x_2426_, v___x_2446_, v___x_2426_, v___x_2426_, v___x_2426_, v___x_2426_, v___x_2426_);
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2421_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2403_);
v___x_2452_ = l_Lean_mkIdent(v_auxFunName_2403_);
v___x_2453_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2451_, v___x_2452_, v___x_2426_);
v___x_2454_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2455_ = l_Array_append___redArg(v___x_2425_, v_binders_2414_);
lean_dec_ref(v_binders_2414_);
v___x_2456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2421_);
lean_ctor_set(v___x_2456_, 1, v___x_2424_);
lean_ctor_set(v___x_2456_, 2, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2458_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2421_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2461_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2420_);
lean_inc(v_quotContext_2419_);
v___x_2462_ = l_Lean_addMacroScope(v_quotContext_2419_, v___x_2461_, v_currMacroScope_2420_);
v___x_2463_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2464_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2421_);
lean_ctor_set(v___x_2464_, 1, v___x_2460_);
lean_ctor_set(v___x_2464_, 2, v___x_2462_);
lean_ctor_set(v___x_2464_, 3, v___x_2463_);
v___x_2465_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2457_, v___x_2459_, v___x_2464_);
v___x_2466_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2424_, v___x_2465_);
v___x_2467_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2454_, v___x_2456_, v___x_2466_);
v___x_2468_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2421_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2472_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2471_, v___x_2426_, v___x_2426_);
v___x_2473_ = l_Lean_Syntax_node4(v___x_2421_, v___x_2468_, v___x_2470_, v_body_2411_, v___x_2472_, v___x_2426_);
v___x_2474_ = l_Lean_Syntax_node5(v___x_2421_, v___x_2448_, v___x_2450_, v___x_2453_, v___x_2467_, v___x_2473_, v___x_2426_);
v___x_2475_ = l_Lean_Syntax_node2(v___x_2421_, v___x_2422_, v___x_2447_, v___x_2474_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2475_);
v___x_2477_ = v___x_2408_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_toCold_2484_; lean_object* v_binders_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2557_; 
v_toCold_2484_ = lean_ctor_get(v___y_2412_, 0);
v_binders_2485_ = lean_ctor_get(v_a_2406_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2558_ = lean_ctor_get(v_a_2406_, 3);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_a_2406_, 2);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_a_2406_, 1);
lean_dec(v_unused_2560_);
v___x_2487_ = v_a_2406_;
v_isShared_2488_ = v_isSharedCheck_2557_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_binders_2485_);
lean_dec(v_a_2406_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2557_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_ref_2489_; lean_object* v_quotContext_2490_; lean_object* v_currMacroScope_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v_ref_2489_ = lean_ctor_get(v___y_2412_, 2);
v_quotContext_2490_ = lean_ctor_get(v_toCold_2484_, 8);
v_currMacroScope_2491_ = lean_ctor_get(v_toCold_2484_, 9);
v___x_2492_ = 0;
v___x_2493_ = l_Lean_SourceInfo_fromRef(v_ref_2489_, v___x_2492_);
v___x_2494_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2495_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2496_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2497_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2493_, 4);
v___x_2498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2493_);
lean_ctor_set(v___x_2498_, 1, v___x_2496_);
lean_ctor_set(v___x_2498_, 2, v___x_2497_);
v___x_2499_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2500_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2493_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2503_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2498_);
v___x_2504_ = l_Lean_Syntax_node1(v___x_2493_, v___x_2503_, v___x_2498_);
v___x_2505_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2506_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2507_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2491_);
lean_inc(v_quotContext_2490_);
v___x_2508_ = l_Lean_addMacroScope(v_quotContext_2490_, v___x_2507_, v_currMacroScope_2491_);
v___x_2509_ = lean_box(0);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 3);
lean_ctor_set(v___x_2487_, 3, v___x_2509_);
lean_ctor_set(v___x_2487_, 2, v___x_2508_);
lean_ctor_set(v___x_2487_, 1, v___x_2506_);
lean_ctor_set(v___x_2487_, 0, v___x_2493_);
v___x_2511_ = v___x_2487_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_inc_ref_n(v___x_2498_, 10);
lean_inc_n(v___x_2493_, 22);
v___x_2512_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2505_, v___x_2511_, v___x_2498_);
v___x_2513_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2502_, v___x_2504_, v___x_2512_);
v___x_2514_ = l_Lean_Syntax_node1(v___x_2493_, v___x_2496_, v___x_2513_);
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2493_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = l_Lean_Syntax_node3(v___x_2493_, v___x_2499_, v___x_2501_, v___x_2514_, v___x_2516_);
v___x_2518_ = l_Lean_Syntax_node1(v___x_2493_, v___x_2496_, v___x_2517_);
v___x_2519_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41));
v___x_2520_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42));
v___x_2521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2493_);
lean_ctor_set(v___x_2521_, 1, v___x_2519_);
v___x_2522_ = l_Lean_Syntax_node1(v___x_2493_, v___x_2520_, v___x_2521_);
v___x_2523_ = l_Lean_Syntax_node1(v___x_2493_, v___x_2496_, v___x_2522_);
v___x_2524_ = l_Lean_Syntax_node7(v___x_2493_, v___x_2495_, v___x_2498_, v___x_2518_, v___x_2498_, v___x_2498_, v___x_2498_, v___x_2498_, v___x_2523_);
v___x_2525_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2526_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2493_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2403_);
v___x_2529_ = l_Lean_mkIdent(v_auxFunName_2403_);
v___x_2530_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2528_, v___x_2529_, v___x_2498_);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2532_ = l_Array_append___redArg(v___x_2497_, v_binders_2485_);
lean_dec_ref(v_binders_2485_);
v___x_2533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2493_);
lean_ctor_set(v___x_2533_, 1, v___x_2496_);
lean_ctor_set(v___x_2533_, 2, v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2493_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2538_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2491_);
lean_inc(v_quotContext_2490_);
v___x_2539_ = l_Lean_addMacroScope(v_quotContext_2490_, v___x_2538_, v_currMacroScope_2491_);
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2541_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2493_);
lean_ctor_set(v___x_2541_, 1, v___x_2537_);
lean_ctor_set(v___x_2541_, 2, v___x_2539_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
v___x_2542_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2534_, v___x_2536_, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_node1(v___x_2493_, v___x_2496_, v___x_2542_);
v___x_2544_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2531_, v___x_2533_, v___x_2543_);
v___x_2545_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2546_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2493_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2549_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2548_, v___x_2498_, v___x_2498_);
v___x_2550_ = l_Lean_Syntax_node4(v___x_2493_, v___x_2545_, v___x_2547_, v_body_2411_, v___x_2549_, v___x_2498_);
v___x_2551_ = l_Lean_Syntax_node5(v___x_2493_, v___x_2525_, v___x_2527_, v___x_2530_, v___x_2544_, v___x_2550_, v___x_2498_);
v___x_2552_ = l_Lean_Syntax_node2(v___x_2493_, v___x_2494_, v___x_2524_, v___x_2551_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2552_);
v___x_2554_ = v___x_2408_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
v_a_2579_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2405_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2405_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object* v_ctx_2587_, lean_object* v_i_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2587_, v_i_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_i_2588_);
lean_dec_ref(v_ctx_2587_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2597_, lean_object* v_ctx_2598_, lean_object* v_a_2599_, lean_object* v_b_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_nat_dec_lt(v_a_2599_, v_upperBound_2597_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
lean_dec(v_a_2599_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_b_2600_);
return v___x_2609_;
}
else
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2598_, v_a_2599_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = lean_array_push(v_b_2600_, v_a_2611_);
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_add(v_a_2599_, v___x_2613_);
lean_dec(v_a_2599_);
v_a_2599_ = v___x_2614_;
v_b_2600_ = v___x_2612_;
goto _start;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_b_2600_);
lean_dec(v_a_2599_);
v_a_2616_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2610_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2610_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2624_, lean_object* v_ctx_2625_, lean_object* v_a_2626_, lean_object* v_b_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2624_, v_ctx_2625_, v_a_2626_, v_b_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v_ctx_2625_);
lean_dec(v_upperBound_2624_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object* v_ctx_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_typeInfos_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v_auxDefs_2654_; lean_object* v___x_2655_; 
v_typeInfos_2651_ = lean_ctor_get(v_ctx_2643_, 1);
v___x_2652_ = lean_array_get_size(v_typeInfos_2651_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v_auxDefs_2654_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v___x_2652_, v_ctx_2643_, v___x_2653_, v_auxDefs_2654_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2676_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2676_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2676_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_ref_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v_ref_2660_ = lean_ctor_get(v_a_2648_, 2);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_SourceInfo_fromRef(v_ref_2660_, v___x_2661_);
v___x_2663_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0));
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1));
lean_inc_n(v___x_2662_, 3);
v___x_2665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2662_);
lean_ctor_set(v___x_2665_, 1, v___x_2663_);
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2667_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2668_ = l_Array_append___redArg(v___x_2667_, v_a_2656_);
lean_dec(v_a_2656_);
v___x_2669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2662_);
lean_ctor_set(v___x_2669_, 1, v___x_2666_);
lean_ctor_set(v___x_2669_, 2, v___x_2668_);
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2));
v___x_2671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2662_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_Syntax_node3(v___x_2662_, v___x_2664_, v___x_2665_, v___x_2669_, v___x_2671_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2672_);
v___x_2674_ = v___x_2658_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2655_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2655_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object* v_ctx_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_ctx_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec_ref(v_ctx_2685_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object* v_upperBound_2694_, lean_object* v_ctx_2695_, lean_object* v_inst_2696_, lean_object* v_R_2697_, lean_object* v_a_2698_, lean_object* v_b_2699_, lean_object* v_c_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2694_, v_ctx_2695_, v_a_2698_, v_b_2699_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2709_, lean_object* v_ctx_2710_, lean_object* v_inst_2711_, lean_object* v_R_2712_, lean_object* v_a_2713_, lean_object* v_b_2714_, lean_object* v_c_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(v_upperBound_2709_, v_ctx_2710_, v_inst_2711_, v_R_2712_, v_a_2713_, v_b_2714_, v_c_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v_ctx_2710_);
lean_dec(v_upperBound_2709_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
if (lean_obj_tag(v_a_2724_) == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = l_List_reverse___redArg(v_a_2725_);
return v___x_2726_;
}
else
{
lean_object* v_head_2727_; lean_object* v_tail_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2737_; 
v_head_2727_ = lean_ctor_get(v_a_2724_, 0);
v_tail_2728_ = lean_ctor_get(v_a_2724_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_a_2724_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2730_ = v_a_2724_;
v_isShared_2731_ = v_isSharedCheck_2737_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_tail_2728_);
lean_inc(v_head_2727_);
lean_dec(v_a_2724_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2737_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = l_Lean_MessageData_ofSyntax(v_head_2727_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v_a_2725_);
lean_ctor_set(v___x_2730_, 0, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_a_2725_);
v___x_2734_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
v_a_2724_ = v_tail_2728_;
v_a_2725_ = v___x_2734_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2738_; double v___x_2739_; 
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = lean_float_of_nat(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object* v_cls_2742_, lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_ref_2749_; lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2796_; 
v_ref_2749_ = lean_ctor_get(v___y_2746_, 2);
v___x_2750_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2796_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2796_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v_traceState_2756_; lean_object* v_env_2757_; lean_object* v_nextMacroScope_2758_; lean_object* v_ngen_2759_; lean_object* v_auxDeclNGen_2760_; lean_object* v_cache_2761_; lean_object* v_recordedDeps_2762_; lean_object* v_messages_2763_; lean_object* v_infoState_2764_; lean_object* v_snapshotTasks_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2795_; 
v___x_2755_ = lean_st_ref_take(v___y_2747_);
v_traceState_2756_ = lean_ctor_get(v___x_2755_, 4);
v_env_2757_ = lean_ctor_get(v___x_2755_, 0);
v_nextMacroScope_2758_ = lean_ctor_get(v___x_2755_, 1);
v_ngen_2759_ = lean_ctor_get(v___x_2755_, 2);
v_auxDeclNGen_2760_ = lean_ctor_get(v___x_2755_, 3);
v_cache_2761_ = lean_ctor_get(v___x_2755_, 5);
v_recordedDeps_2762_ = lean_ctor_get(v___x_2755_, 6);
v_messages_2763_ = lean_ctor_get(v___x_2755_, 7);
v_infoState_2764_ = lean_ctor_get(v___x_2755_, 8);
v_snapshotTasks_2765_ = lean_ctor_get(v___x_2755_, 9);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2767_ = v___x_2755_;
v_isShared_2768_ = v_isSharedCheck_2795_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_snapshotTasks_2765_);
lean_inc(v_infoState_2764_);
lean_inc(v_messages_2763_);
lean_inc(v_recordedDeps_2762_);
lean_inc(v_cache_2761_);
lean_inc(v_traceState_2756_);
lean_inc(v_auxDeclNGen_2760_);
lean_inc(v_ngen_2759_);
lean_inc(v_nextMacroScope_2758_);
lean_inc(v_env_2757_);
lean_dec(v___x_2755_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2795_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
uint64_t v_tid_2769_; lean_object* v_traces_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2794_; 
v_tid_2769_ = lean_ctor_get_uint64(v_traceState_2756_, sizeof(void*)*1);
v_traces_2770_ = lean_ctor_get(v_traceState_2756_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_traceState_2756_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2772_ = v_traceState_2756_;
v_isShared_2773_ = v_isSharedCheck_2794_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_traces_2770_);
lean_dec(v_traceState_2756_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2794_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; double v___x_2776_; uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_box(0);
v___x_2776_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0);
v___x_2777_ = 0;
v___x_2778_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13));
v___x_2779_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2779_, 0, v_cls_2742_);
lean_ctor_set(v___x_2779_, 1, v___x_2775_);
lean_ctor_set(v___x_2779_, 2, v___x_2778_);
lean_ctor_set_float(v___x_2779_, sizeof(void*)*3, v___x_2776_);
lean_ctor_set_float(v___x_2779_, sizeof(void*)*3 + 8, v___x_2776_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*3 + 16, v___x_2777_);
v___x_2780_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1));
v___x_2781_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v_a_2751_);
lean_ctor_set(v___x_2781_, 2, v___x_2780_);
lean_inc(v_ref_2749_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_ref_2749_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_PersistentArray_push___redArg(v_traces_2770_, v___x_2782_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2783_);
v___x_2785_ = v___x_2772_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2783_);
lean_ctor_set_uint64(v_reuseFailAlloc_2793_, sizeof(void*)*1, v_tid_2769_);
v___x_2785_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2787_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 4, v___x_2785_);
v___x_2787_ = v___x_2767_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_env_2757_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_nextMacroScope_2758_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_ngen_2759_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_auxDeclNGen_2760_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2792_, 5, v_cache_2761_);
lean_ctor_set(v_reuseFailAlloc_2792_, 6, v_recordedDeps_2762_);
lean_ctor_set(v_reuseFailAlloc_2792_, 7, v_messages_2763_);
lean_ctor_set(v_reuseFailAlloc_2792_, 8, v_infoState_2764_);
lean_ctor_set(v_reuseFailAlloc_2792_, 9, v_snapshotTasks_2765_);
v___x_2787_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = lean_st_ref_put(v___y_2747_, v___x_2787_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2774_);
v___x_2790_ = v___x_2753_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2774_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object* v_cls_2797_, lean_object* v_msg_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2797_, v_msg_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
return v_res_2804_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2813_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2));
v___x_2814_ = l_Lean_Name_append(v___x_2813_, v___x_2812_);
return v___x_2814_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4));
v___x_2817_ = l_Lean_stringToMessageData(v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object* v_declName_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_2827_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52));
v___x_2828_ = 1;
lean_inc(v_declName_2818_);
v___x_2829_ = l_Lean_Elab_Deriving_mkContext(v___x_2826_, v___x_2827_, v_declName_2818_, v___x_2828_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_a_2830_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_mk_empty_array_with_capacity(v___x_2833_);
lean_inc_ref(v___x_2834_);
v___x_2835_ = lean_array_push(v___x_2834_, v_declName_2818_);
v___x_2836_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_2830_, v___x_2826_, v___x_2835_, v___x_2828_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
lean_dec_ref(v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_toCold_2837_; lean_object* v_options_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2879_; 
v_toCold_2837_ = lean_ctor_get(v_a_2823_, 0);
v_options_2838_ = lean_ctor_get(v_toCold_2837_, 2);
v_a_2839_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2841_ = v___x_2836_;
v_isShared_2842_ = v_isSharedCheck_2879_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2836_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2879_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_inheritedTraceOptions_2843_; uint8_t v_hasTrace_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_inheritedTraceOptions_2843_ = lean_ctor_get(v_toCold_2837_, 11);
v_hasTrace_2844_ = lean_ctor_get_uint8(v_options_2838_, sizeof(void*)*1);
v___x_2845_ = lean_array_push(v___x_2834_, v_a_2832_);
v___x_2846_ = l_Array_append___redArg(v___x_2845_, v_a_2839_);
lean_dec(v_a_2839_);
if (v_hasTrace_2844_ == 0)
{
lean_object* v___x_2848_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2846_);
v___x_2848_ = v___x_2841_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
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
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2851_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3);
v___x_2852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2843_, v_options_2838_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2854_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2846_);
v___x_2854_ = v___x_2841_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2846_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_del_object(v___x_2841_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5);
lean_inc_ref(v___x_2846_);
v___x_2857_ = lean_array_to_list(v___x_2846_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(v___x_2857_, v___x_2858_);
v___x_2860_ = l_Lean_MessageData_ofList(v___x_2859_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2856_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v___x_2850_, v___x_2861_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v___x_2862_, 0);
lean_dec(v_unused_2870_);
v___x_2864_ = v___x_2862_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_dec(v___x_2862_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2846_);
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2846_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v___x_2846_);
v_a_2871_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2862_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2862_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec_ref(v___x_2834_);
lean_dec(v_a_2832_);
v_a_2880_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2836_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2836_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_a_2830_);
lean_dec(v_declName_2818_);
v_a_2888_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2831_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2831_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_declName_2818_);
v_a_2896_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2829_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2829_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object* v_declName_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(v_declName_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object* v_cls_2913_, lean_object* v_msg_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2913_, v_msg_2914_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object* v_cls_2923_, lean_object* v_msg_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(v_cls_2923_, v_msg_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object* v_declName_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; lean_object* v_env_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2936_ = lean_st_ref_get(v___y_2934_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_ref(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2938_ = l_Lean_isInductiveCore(v_env_2937_, v_declName_2933_);
v___x_2939_ = lean_box(v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2941_, v___y_2942_);
lean_dec(v___y_2942_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object* v_declName_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2945_, v___y_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object* v_declName_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(v_declName_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t v_____do__lift_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
if (v_____do__lift_2955_ == 0)
{
uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = 1;
v___x_2960_ = lean_box(v___x_2959_);
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
return v___x_2961_;
}
else
{
uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = 0;
v___x_2963_ = lean_box(v___x_2962_);
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
uint8_t v_____do__lift_2284__boxed_2969_; lean_object* v_res_2970_; 
v_____do__lift_2284__boxed_2969_ = lean_unbox(v_____do__lift_2965_);
v_res_2970_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v_____do__lift_2284__boxed_2969_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object* v_as_2971_, size_t v_i_2972_, size_t v_stop_2973_, lean_object* v_b_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_usize_dec_eq(v_i_2972_, v_stop_2973_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_array_uget_borrowed(v_as_2971_, v_i_2972_);
lean_inc(v___x_2979_);
v___x_2980_ = l_Lean_Elab_Command_elabCommand(v___x_2979_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; size_t v___x_2982_; size_t v___x_2983_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2972_, v___x_2982_);
v_i_2972_ = v___x_2983_;
v_b_2974_ = v_a_2981_;
goto _start;
}
else
{
return v___x_2980_;
}
}
else
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2974_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_stop_2988_, lean_object* v_b_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
size_t v_i_boxed_2993_; size_t v_stop_boxed_2994_; lean_object* v_res_2995_; 
v_i_boxed_2993_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_stop_boxed_2994_ = lean_unbox_usize(v_stop_2988_);
lean_dec(v_stop_2988_);
v_res_2995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_as_2986_, v_i_boxed_2993_, v_stop_boxed_2994_, v_b_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec_ref(v_as_2986_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object* v___x_2996_, lean_object* v___x_2997_, lean_object* v___x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2996_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3015_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3015_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3015_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_array_get_size(v_a_3003_);
v___x_3008_ = lean_nat_dec_lt(v___x_2997_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v_a_3003_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_2998_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2998_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
else
{
size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
lean_del_object(v___x_3005_);
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = lean_usize_of_nat(v___x_3007_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_3003_, v___x_3012_, v___x_3013_, v___x_2998_, v___y_2999_, v___y_3000_);
lean_dec(v_a_3003_);
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
v_a_3016_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3002_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3002_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object* v___x_3024_, lean_object* v___x_3025_, lean_object* v___x_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(v___x_3024_, v___x_3025_, v___x_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___x_3025_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object* v_as_3031_, size_t v_sz_3032_, size_t v_i_3033_, lean_object* v_b_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_usize_dec_lt(v_i_3033_, v_sz_3032_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_b_3034_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___f_3044_; lean_object* v___x_3045_; 
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_box(0);
v_a_3042_ = lean_array_uget_borrowed(v_as_3031_, v_i_3033_);
lean_inc_n(v_a_3042_, 2);
v___x_3043_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed), 8, 1);
lean_closure_set(v___x_3043_, 0, v_a_3042_);
v___f_3044_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3044_, 0, v___x_3043_);
lean_closure_set(v___f_3044_, 1, v___x_3040_);
lean_closure_set(v___f_3044_, 2, v___x_3041_);
v___x_3045_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_3042_, v___f_3044_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3045_) == 0)
{
size_t v___x_3046_; size_t v___x_3047_; 
lean_dec_ref_known(v___x_3045_, 1);
v___x_3046_ = ((size_t)1ULL);
v___x_3047_ = lean_usize_add(v_i_3033_, v___x_3046_);
v_i_3033_ = v___x_3047_;
v_b_3034_ = v___x_3041_;
goto _start;
}
else
{
return v___x_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object* v_as_3049_, lean_object* v_sz_3050_, lean_object* v_i_3051_, lean_object* v_b_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
size_t v_sz_boxed_3056_; size_t v_i_boxed_3057_; lean_object* v_res_3058_; 
v_sz_boxed_3056_ = lean_unbox_usize(v_sz_3050_);
lean_dec(v_sz_3050_);
v_i_boxed_3057_ = lean_unbox_usize(v_i_3051_);
lean_dec(v_i_3051_);
v_res_3058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_as_3049_, v_sz_boxed_3056_, v_i_boxed_3057_, v_b_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec_ref(v_as_3049_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object* v_as_3059_, size_t v_i_3060_, size_t v_stop_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v___x_3065_; 
v___x_3065_ = lean_usize_dec_eq(v_i_3060_, v_stop_3061_);
if (v___x_3065_ == 0)
{
uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = 1;
v___x_3067_ = lean_array_uget_borrowed(v_as_3059_, v_i_3060_);
lean_inc(v___x_3067_);
v___x_3068_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v___x_3067_, v___y_3063_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3081_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3081_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3081_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_unbox(v_a_3069_);
lean_dec(v_a_3069_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3074_ = lean_box(v___x_3066_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3074_);
v___x_3076_ = v___x_3071_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
else
{
size_t v___x_3078_; size_t v___x_3079_; 
lean_del_object(v___x_3071_);
v___x_3078_ = ((size_t)1ULL);
v___x_3079_ = lean_usize_add(v_i_3060_, v___x_3078_);
v_i_3060_ = v___x_3079_;
goto _start;
}
}
}
else
{
return v___x_3068_;
}
}
else
{
uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = 0;
v___x_3083_ = lean_box(v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object* v_as_3085_, lean_object* v_i_3086_, lean_object* v_stop_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
size_t v_i_boxed_3091_; size_t v_stop_boxed_3092_; lean_object* v_res_3093_; 
v_i_boxed_3091_ = lean_unbox_usize(v_i_3086_);
lean_dec(v_i_3086_);
v_stop_boxed_3092_ = lean_unbox_usize(v_stop_3087_);
lean_dec(v_stop_3087_);
v_res_3093_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_as_3085_, v_i_boxed_3091_, v_stop_boxed_3092_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec_ref(v_as_3085_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object* v_declNames_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v___y_3122_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3125_ = lean_unsigned_to_nat(0u);
v___x_3126_ = lean_array_get_size(v_declNames_3094_);
v___x_3127_ = lean_nat_dec_lt(v___x_3125_, v___x_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3127_, v_a_3095_, v_a_3096_);
v___y_3122_ = v___x_3128_;
goto v___jp_3121_;
}
else
{
if (v___x_3127_ == 0)
{
goto v___jp_3098_;
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = lean_usize_of_nat(v___x_3126_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_declNames_3094_, v___x_3129_, v___x_3130_, v_a_3095_, v_a_3096_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; uint8_t v___x_3133_; lean_object* v___x_3134_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v___x_3133_ = lean_unbox(v_a_3132_);
lean_dec(v_a_3132_);
v___x_3134_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3133_, v_a_3095_, v_a_3096_);
v___y_3122_ = v___x_3134_;
goto v___jp_3121_;
}
else
{
return v___x_3131_;
}
}
}
v___jp_3098_:
{
uint8_t v___x_3099_; lean_object* v___x_3100_; size_t v_sz_3101_; size_t v___x_3102_; lean_object* v___x_3103_; 
v___x_3099_ = 1;
v___x_3100_ = lean_box(0);
v_sz_3101_ = lean_array_size(v_declNames_3094_);
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_declNames_3094_, v_sz_3101_, v___x_3102_, v___x_3100_, v_a_3095_, v_a_3096_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3103_, 0);
lean_dec(v_unused_3112_);
v___x_3105_ = v___x_3103_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v___x_3103_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_box(v___x_3099_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_a_3113_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3103_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3103_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
v___jp_3121_:
{
lean_object* v_a_3123_; uint8_t v___x_3124_; 
v_a_3123_ = lean_ctor_get(v___y_3122_, 0);
v___x_3124_ = lean_unbox(v_a_3123_);
if (v___x_3124_ == 0)
{
return v___y_3122_;
}
else
{
lean_dec_ref(v___y_3122_);
goto v___jp_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object* v_declNames_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(v_declNames_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec_ref(v_declNames_3135_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_3208_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3209_ = l_Lean_Elab_registerDerivingHandler(v___x_3207_, v___x_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; uint8_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref_known(v___x_3209_, 1);
v___x_3210_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_3211_ = 0;
v___x_3212_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3213_ = l_Lean_registerTraceClass(v___x_3210_, v___x_3211_, v___x_3212_);
return v___x_3213_;
}
else
{
return v___x_3209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
return v_res_3215_;
}
}
lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Repr(builtin);
}
#ifdef __cplusplus
}
#endif
