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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 44, 178, 157, 49, 38, 131, 220)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Format.group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(199, 101, 149, 40, 211, 134, 215, 211)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(244, 69, 187, 229, 60, 74, 115, 66)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(8, 121, 197, 203, 165, 174, 61, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(179, 146, 214, 149, 195, 116, 102, 235)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(248, 109, 138, 163, 21, 170, 71, 243)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\"_\""};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 237, 177, 226, 131, 244, 212, 161)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
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
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 110, 112, 1, 140, 132, 234, 227)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
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
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(174, 48, 2, 244, 180, 197, 18, 79)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
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
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 42, 41, 58, 31, 42, 63)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
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
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(224, 137, 43, 251, 2, 178, 60, 92)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 224, 49, 20, 188, 146, 89, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 160, 169, 100, 58, 75, 239, 18)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 81, 7, 4, 169, 73, 180)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(231, 58, 223, 30, 148, 240, 234, 38)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(225, 21, 194, 109, 33, 15, 109, 4)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(69, 90, 211, 79, 166, 122, 95, 47)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 118, 68, 66, 204, 66, 159)}};
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
lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object* v_indVal_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
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
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkReprHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_44_ = stack[0].m_obj;
lean_object* v_a_45_ = stack[1].m_obj;
lean_object* v_a_46_ = stack[2].m_obj;
lean_object* v_a_47_ = stack[3].m_obj;
lean_object* v_a_48_ = stack[4].m_obj;
lean_object* v_a_49_ = stack[5].m_obj;
lean_object* v_a_50_ = stack[6].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object* v_indVal_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
return v_res_113_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(lean_object* v_k_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v_b_117_, lean_object* v_c_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
v___x_124_ = lean_apply_9(v_k_114_, v_b_117_, v_c_118_, v___y_115_, v___y_116_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, lean_box(0));
return v___x_124_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_114_ = stack[0].m_obj;
lean_object* v___y_115_ = stack[1].m_obj;
lean_object* v___y_116_ = stack[2].m_obj;
lean_object* v_b_117_ = stack[3].m_obj;
lean_object* v_c_118_ = stack[4].m_obj;
lean_object* v___y_119_ = stack[5].m_obj;
lean_object* v___y_120_ = stack[6].m_obj;
lean_object* v___y_121_ = stack[7].m_obj;
lean_object* v___y_122_ = stack[8].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(v_k_114_, v___y_115_, v___y_116_, v_b_117_, v_c_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed(lean_object* v_k_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v_b_129_, lean_object* v_c_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(v_k_126_, v___y_127_, v___y_128_, v_b_129_, v_c_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_136_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(lean_object* v_type_137_, lean_object* v_k_138_, uint8_t v_cleanupAnnotations_139_, uint8_t v_whnfType_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; 
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_148_, 0, v_k_138_);
lean_closure_set(v___f_148_, 1, v___y_141_);
lean_closure_set(v___f_148_, 2, v___y_142_);
v___x_149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_137_, v___f_148_, v_cleanupAnnotations_139_, v_whnfType_140_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_149_) == 0)
{
return v___x_149_;
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_137_ = stack[0].m_obj;
lean_object* v_k_138_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_139_ = stack[2].m_num;
uint8_t v_whnfType_140_ = stack[3].m_num;
lean_object* v___y_141_ = stack[4].m_obj;
lean_object* v___y_142_ = stack[5].m_obj;
lean_object* v___y_143_ = stack[6].m_obj;
lean_object* v___y_144_ = stack[7].m_obj;
lean_object* v___y_145_ = stack[8].m_obj;
lean_object* v___y_146_ = stack[9].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_137_, v_k_138_, v_cleanupAnnotations_139_, v_whnfType_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___boxed(lean_object* v_type_159_, lean_object* v_k_160_, lean_object* v_cleanupAnnotations_161_, lean_object* v_whnfType_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_170_; uint8_t v_whnfType_boxed_171_; lean_object* v_res_172_; 
v_cleanupAnnotations_boxed_170_ = lean_unbox(v_cleanupAnnotations_161_);
v_whnfType_boxed_171_ = lean_unbox(v_whnfType_162_);
v_res_172_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_159_, v_k_160_, v_cleanupAnnotations_boxed_170_, v_whnfType_boxed_171_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_172_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(lean_object* v_00_u03b1_173_, lean_object* v_type_174_, lean_object* v_k_175_, uint8_t v_cleanupAnnotations_176_, uint8_t v_whnfType_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_174_, v_k_175_, v_cleanupAnnotations_176_, v_whnfType_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_174_ = stack[1].m_obj;
lean_object* v_k_175_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_176_ = stack[3].m_num;
uint8_t v_whnfType_177_ = stack[4].m_num;
lean_object* v___y_178_ = stack[5].m_obj;
lean_object* v___y_179_ = stack[6].m_obj;
lean_object* v___y_180_ = stack[7].m_obj;
lean_object* v___y_181_ = stack[8].m_obj;
lean_object* v___y_182_ = stack[9].m_obj;
lean_object* v___y_183_ = stack[10].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(lean_box(0), v_type_174_, v_k_175_, v_cleanupAnnotations_176_, v_whnfType_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___boxed(lean_object* v_00_u03b1_187_, lean_object* v_type_188_, lean_object* v_k_189_, lean_object* v_cleanupAnnotations_190_, lean_object* v_whnfType_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_199_; uint8_t v_whnfType_boxed_200_; lean_object* v_res_201_; 
v_cleanupAnnotations_boxed_199_ = lean_unbox(v_cleanupAnnotations_190_);
v_whnfType_boxed_200_ = lean_unbox(v_whnfType_191_);
v_res_201_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(v_00_u03b1_187_, v_type_188_, v_k_189_, v_cleanupAnnotations_boxed_199_, v_whnfType_boxed_200_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_201_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(1);
v___x_203_ = l_Lean_MessageData_ofFormat(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2));
v___x_208_ = l_Lean_MessageData_ofFormat(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
return v_x_209_;
}
else
{
lean_object* v_head_211_; lean_object* v_tail_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_234_; 
v_head_211_ = lean_ctor_get(v_x_210_, 0);
v_tail_212_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_234_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_234_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_tail_212_);
lean_inc(v_head_211_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_234_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_before_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_232_; 
v_before_216_ = lean_ctor_get(v_head_211_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_head_211_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v_head_211_, 1);
lean_dec(v_unused_233_);
v___x_218_ = v_head_211_;
v_isShared_219_ = v_isSharedCheck_232_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_before_216_);
lean_dec(v_head_211_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_232_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 7);
lean_ctor_set(v___x_218_, 1, v___x_220_);
lean_ctor_set(v___x_218_, 0, v_x_209_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_x_209_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_231_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 7);
lean_ctor_set(v___x_214_, 1, v___x_223_);
lean_ctor_set(v___x_214_, 0, v___x_222_);
v___x_225_ = v___x_214_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_230_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = l_Lean_MessageData_ofSyntax(v_before_216_);
v___x_227_ = l_Lean_indentD(v___x_226_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_225_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v_x_209_ = v___x_228_;
v_x_210_ = v_tail_212_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(lean_object* v_opts_235_, lean_object* v_opt_236_){
_start:
{
lean_object* v_name_237_; lean_object* v_defValue_238_; lean_object* v_map_239_; lean_object* v___x_240_; 
v_name_237_ = lean_ctor_get(v_opt_236_, 0);
v_defValue_238_ = lean_ctor_get(v_opt_236_, 1);
v_map_239_ = lean_ctor_get(v_opts_235_, 0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_239_, v_name_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
uint8_t v___x_241_; 
v___x_241_ = lean_unbox(v_defValue_238_);
return v___x_241_;
}
else
{
lean_object* v_val_242_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_240_, 1);
if (lean_obj_tag(v_val_242_) == 1)
{
uint8_t v_v_243_; 
v_v_243_ = lean_ctor_get_uint8(v_val_242_, 0);
lean_dec_ref_known(v_val_242_, 0);
return v_v_243_;
}
else
{
uint8_t v___x_244_; 
lean_dec(v_val_242_);
v___x_244_ = lean_unbox(v_defValue_238_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_235_ = stack[0].m_obj;
lean_object* v_opt_236_ = stack[1].m_obj;
uint8_t v_res_245_;
v_res_245_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_opts_235_, v_opt_236_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_opts_246_, v_opt_247_);
lean_dec_ref(v_opt_247_);
lean_dec_ref(v_opts_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1));
v___x_254_ = l_Lean_MessageData_ofFormat(v___x_253_);
return v___x_254_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(lean_object* v_msgData_255_, lean_object* v_macroStack_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_259_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_257_);
v___x_260_ = l_Lean_Elab_pp_macroStack;
v___x_261_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v___x_259_, v___x_260_);
lean_dec_ref(v___x_259_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec(v_macroStack_256_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_msgData_255_);
return v___x_262_;
}
else
{
if (lean_obj_tag(v_macroStack_256_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_msgData_255_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_after_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_280_; 
v_head_264_ = lean_ctor_get(v_macroStack_256_, 0);
lean_inc(v_head_264_);
v_after_265_ = lean_ctor_get(v_head_264_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_head_264_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_head_264_, 0);
lean_dec(v_unused_281_);
v___x_267_ = v_head_264_;
v_isShared_268_ = v_isSharedCheck_280_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_after_265_);
lean_dec(v_head_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_280_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 7);
lean_ctor_set(v___x_267_, 1, v___x_269_);
lean_ctor_set(v___x_267_, 0, v_msgData_255_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_msgData_255_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_269_);
v___x_271_ = v_reuseFailAlloc_279_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_msgData_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_272_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2);
v___x_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = l_Lean_MessageData_ofSyntax(v_after_265_);
v___x_275_ = l_Lean_indentD(v___x_274_);
v_msgData_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_276_, 0, v___x_273_);
lean_ctor_set(v_msgData_276_, 1, v___x_275_);
v___x_277_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(v_msgData_276_, v_macroStack_256_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_255_ = stack[0].m_obj;
lean_object* v_macroStack_256_ = stack[1].m_obj;
lean_object* v___y_257_ = stack[2].m_obj;
lean_object* v_res_282_;
v_res_282_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_255_, v_macroStack_256_, v___y_257_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_283_, lean_object* v_macroStack_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_283_, v_macroStack_284_, v___y_285_);
lean_dec_ref(v___y_285_);
return v_res_287_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(lean_object* v_msgData_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; lean_object* v_env_295_; uint8_t v___x_296_; lean_object* v_env_297_; lean_object* v___x_298_; lean_object* v_toCold_299_; lean_object* v_mctx_300_; lean_object* v_lctx_301_; lean_object* v_options_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_294_ = lean_st_ref_get(v___y_292_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v___x_296_ = 0;
v_env_297_ = l_Lean_Environment_setRecordingDeps(v_env_295_, v___x_296_);
v___x_298_ = lean_st_ref_get(v___y_290_);
v_toCold_299_ = lean_ctor_get(v___y_291_, 0);
v_mctx_300_ = lean_ctor_get(v___x_298_, 0);
lean_inc_ref(v_mctx_300_);
lean_dec(v___x_298_);
v_lctx_301_ = lean_ctor_get(v___y_289_, 2);
v_options_302_ = lean_ctor_get(v_toCold_299_, 2);
lean_inc_ref(v_options_302_);
lean_inc_ref(v_lctx_301_);
v___x_303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_303_, 0, v_env_297_);
lean_ctor_set(v___x_303_, 1, v_mctx_300_);
lean_ctor_set(v___x_303_, 2, v_lctx_301_);
lean_ctor_set(v___x_303_, 3, v_options_302_);
v___x_304_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_msgData_288_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_288_ = stack[0].m_obj;
lean_object* v___y_289_ = stack[1].m_obj;
lean_object* v___y_290_ = stack[2].m_obj;
lean_object* v___y_291_ = stack[3].m_obj;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msgData_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4___boxed(lean_object* v_msgData_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msgData_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_313_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_ref_322_; lean_object* v_macroStack_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_ref_322_ = lean_ctor_get(v___y_319_, 2);
v_macroStack_323_ = lean_ctor_get(v___y_315_, 1);
v___x_324_ = l_Lean_Elab_getBetterRef(v_ref_322_, v_macroStack_323_);
v___x_325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_314_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_325_);
lean_inc(v_macroStack_323_);
v___x_327_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_a_326_, v_macroStack_323_, v___y_319_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_324_);
lean_ctor_set(v___x_332_, 1, v_a_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 1);
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_314_ = stack[0].m_obj;
lean_object* v___y_315_ = stack[1].m_obj;
lean_object* v___y_316_ = stack[2].m_obj;
lean_object* v___y_317_ = stack[3].m_obj;
lean_object* v___y_318_ = stack[4].m_obj;
lean_object* v___y_319_ = stack[5].m_obj;
lean_object* v___y_320_ = stack[6].m_obj;
lean_object* v_res_337_;
v_res_337_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object* v_msg_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
uint8_t v_decide_351_; 
v_decide_351_ = lean_nat_dec_eq(v_a_349_, v___x_347_);
if (v_decide_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_string_utf8_next_fast(v___x_348_, v_a_349_);
lean_dec(v_a_349_);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_b_350_, v___x_353_);
lean_dec(v_b_350_);
v_a_349_ = v___x_352_;
v_b_350_ = v___x_354_;
goto _start;
}
else
{
lean_dec(v_a_349_);
return v_b_350_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object* v___x_356_, lean_object* v___x_357_, lean_object* v_a_358_, lean_object* v_b_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_356_, v___x_357_, v_a_358_, v_b_359_);
lean_dec_ref(v___x_357_);
lean_dec(v___x_356_);
return v_res_360_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12));
v___x_386_ = l_String_toRawSubstring_x27(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32));
v___x_433_ = l_String_toRawSubstring_x27(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42));
v___x_456_ = l_String_toRawSubstring_x27(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51));
v___x_478_ = l_String_toRawSubstring_x27(v___x_477_);
return v___x_478_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___f_498_, lean_object* v___x_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v_____r_503_, lean_object* v_fields_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___y_513_; lean_object* v___x_639_; 
lean_inc_ref(v___x_502_);
v___x_639_ = l_Lean_Meta_isType(v___x_502_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; uint8_t v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v___x_641_ = lean_unbox(v_a_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec_ref_known(v___x_639_, 1);
v___x_642_ = l_Lean_Meta_isProof(v___x_502_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
v___y_513_ = v___x_642_;
goto v___jp_512_;
}
else
{
lean_dec_ref(v___x_502_);
v___y_513_ = v___x_639_;
goto v___jp_512_;
}
}
else
{
lean_dec_ref(v___x_502_);
v___y_513_ = v___x_639_;
goto v___jp_512_;
}
v___jp_512_:
{
if (lean_obj_tag(v___y_513_) == 0)
{
lean_object* v_a_514_; uint8_t v___x_515_; 
v_a_514_ = lean_ctor_get(v___y_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___y_513_, 1);
v___x_515_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_516_ = lean_string_utf8_byte_size(v___x_495_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_516_, v___x_495_, v___x_517_, v___x_496_);
v___x_519_ = lean_unsigned_to_nat(4u);
v___x_520_ = lean_nat_add(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
v___x_521_ = l_Nat_reprFast(v___x_520_);
v___x_522_ = l_Lean_Syntax_mkNumLit(v___x_521_, v___x_497_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
v___x_523_ = lean_apply_7(v___f_498_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, lean_box(0));
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_toCold_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_591_; 
v_toCold_524_ = lean_ctor_get(v___y_509_, 0);
v_a_525_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_591_ == 0)
{
v___x_527_ = v___x_523_;
v_isShared_528_ = v_isSharedCheck_591_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_591_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_quotContext_529_; lean_object* v_currMacroScope_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_quotContext_529_ = lean_ctor_get(v_toCold_524_, 8);
v_currMacroScope_530_ = lean_ctor_get(v_toCold_524_, 9);
v___x_531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_525_, 25);
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v_a_525_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_inc_ref_n(v___x_533_, 2);
v___x_534_ = l_Lean_Syntax_node3(v_a_525_, v___x_531_, v_fields_504_, v___x_533_, v___x_499_);
v___x_535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_536_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5));
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_525_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_Syntax_node1(v_a_525_, v___x_535_, v___x_537_);
v___x_539_ = l_Lean_Syntax_node3(v_a_525_, v___x_531_, v___x_534_, v___x_533_, v___x_538_);
v___x_540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7));
v___x_541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9));
v___x_542_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v_a_525_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11));
v___x_545_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13);
v___x_546_ = lean_box(0);
lean_inc_n(v_currMacroScope_530_, 4);
lean_inc_n(v_quotContext_529_, 4);
v___x_547_ = l_Lean_addMacroScope(v_quotContext_529_, v___x_546_, v_currMacroScope_530_);
v___x_548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29));
v___x_549_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_549_, 0, v_a_525_);
lean_ctor_set(v___x_549_, 1, v___x_545_);
lean_ctor_set(v___x_549_, 2, v___x_547_);
lean_ctor_set(v___x_549_, 3, v___x_548_);
v___x_550_ = l_Lean_Syntax_node1(v_a_525_, v___x_544_, v___x_549_);
v___x_551_ = l_Lean_Syntax_node2(v_a_525_, v___x_541_, v___x_543_, v___x_550_);
v___x_552_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31));
v___x_553_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33);
v___x_554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36));
v___x_555_ = l_Lean_addMacroScope(v_quotContext_529_, v___x_554_, v_currMacroScope_530_);
v___x_556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41));
v___x_557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_557_, 0, v_a_525_);
lean_ctor_set(v___x_557_, 1, v___x_553_);
lean_ctor_set(v___x_557_, 2, v___x_555_);
lean_ctor_set(v___x_557_, 3, v___x_556_);
v___x_558_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_559_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43);
v___x_560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45));
v___x_561_ = l_Lean_addMacroScope(v_quotContext_529_, v___x_560_, v_currMacroScope_530_);
v___x_562_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50));
v___x_563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_563_, 0, v_a_525_);
lean_ctor_set(v___x_563_, 1, v___x_559_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
v___x_564_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52);
v___x_565_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53));
v___x_566_ = l_Lean_addMacroScope(v_quotContext_529_, v___x_565_, v_currMacroScope_530_);
v___x_567_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55));
v___x_568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_568_, 0, v_a_525_);
lean_ctor_set(v___x_568_, 1, v___x_564_);
lean_ctor_set(v___x_568_, 2, v___x_566_);
lean_ctor_set(v___x_568_, 3, v___x_567_);
v___x_569_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57));
v___x_570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58));
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_525_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_mkIdent(v___x_500_);
v___x_573_ = l_Lean_Syntax_node3(v_a_525_, v___x_569_, v___x_501_, v___x_571_, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v_a_525_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
lean_inc_ref_n(v___x_575_, 3);
lean_inc_n(v___x_551_, 3);
v___x_576_ = l_Lean_Syntax_node3(v_a_525_, v___x_540_, v___x_551_, v___x_573_, v___x_575_);
v___x_577_ = l_Lean_Syntax_node1(v_a_525_, v___x_558_, v___x_576_);
v___x_578_ = l_Lean_Syntax_node2(v_a_525_, v___x_552_, v___x_568_, v___x_577_);
v___x_579_ = l_Lean_Syntax_node3(v_a_525_, v___x_540_, v___x_551_, v___x_578_, v___x_575_);
v___x_580_ = l_Lean_Syntax_node2(v_a_525_, v___x_558_, v___x_522_, v___x_579_);
v___x_581_ = l_Lean_Syntax_node2(v_a_525_, v___x_552_, v___x_563_, v___x_580_);
v___x_582_ = l_Lean_Syntax_node3(v_a_525_, v___x_540_, v___x_551_, v___x_581_, v___x_575_);
v___x_583_ = l_Lean_Syntax_node1(v_a_525_, v___x_558_, v___x_582_);
v___x_584_ = l_Lean_Syntax_node2(v_a_525_, v___x_552_, v___x_557_, v___x_583_);
v___x_585_ = l_Lean_Syntax_node3(v_a_525_, v___x_540_, v___x_551_, v___x_584_, v___x_575_);
v___x_586_ = l_Lean_Syntax_node3(v_a_525_, v___x_531_, v___x_539_, v___x_533_, v___x_585_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_587_);
v___x_589_ = v___x_527_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v___x_522_);
lean_dec(v_fields_504_);
lean_dec(v___x_501_);
lean_dec(v___x_500_);
lean_dec(v___x_499_);
v_a_592_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_523_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_523_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_600_; 
lean_dec(v___x_501_);
lean_dec(v___x_500_);
lean_dec(v___x_497_);
lean_dec(v___x_496_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
v___x_600_ = lean_apply_7(v___f_498_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, lean_box(0));
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_622_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_622_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_622_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_622_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_605_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_606_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_601_, 7);
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v_a_601_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_inc_ref_n(v___x_607_, 2);
v___x_608_ = l_Lean_Syntax_node3(v_a_601_, v___x_605_, v_fields_504_, v___x_607_, v___x_499_);
v___x_609_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_610_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5));
v___x_611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_611_, 0, v_a_601_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_Syntax_node1(v_a_601_, v___x_609_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node3(v_a_601_, v___x_605_, v___x_608_, v___x_607_, v___x_612_);
v___x_614_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59));
v___x_615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_615_, 0, v_a_601_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_Syntax_node1(v_a_601_, v___x_609_, v___x_615_);
v___x_617_ = l_Lean_Syntax_node3(v_a_601_, v___x_605_, v___x_613_, v___x_607_, v___x_616_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_618_);
v___x_620_ = v___x_603_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_fields_504_);
lean_dec(v___x_499_);
v_a_623_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_600_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_600_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_fields_504_);
lean_dec(v___x_501_);
lean_dec(v___x_500_);
lean_dec(v___x_499_);
lean_dec_ref(v___f_498_);
lean_dec(v___x_497_);
lean_dec(v___x_496_);
v_a_631_ = lean_ctor_get(v___y_513_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___y_513_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___y_513_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___y_513_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_495_ = stack[0].m_obj;
lean_object* v___x_496_ = stack[1].m_obj;
lean_object* v___x_497_ = stack[2].m_obj;
lean_object* v___f_498_ = stack[3].m_obj;
lean_object* v___x_499_ = stack[4].m_obj;
lean_object* v___x_500_ = stack[5].m_obj;
lean_object* v___x_501_ = stack[6].m_obj;
lean_object* v___x_502_ = stack[7].m_obj;
lean_object* v_____r_503_ = stack[8].m_obj;
lean_object* v_fields_504_ = stack[9].m_obj;
lean_object* v___y_505_ = stack[10].m_obj;
lean_object* v___y_506_ = stack[11].m_obj;
lean_object* v___y_507_ = stack[12].m_obj;
lean_object* v___y_508_ = stack[13].m_obj;
lean_object* v___y_509_ = stack[14].m_obj;
lean_object* v___y_510_ = stack[15].m_obj;
lean_object* v_res_643_;
v_res_643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___x_495_, v___x_496_, v___x_497_, v___f_498_, v___x_499_, v___x_500_, v___x_501_, v___x_502_, v_____r_503_, v_fields_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_644_ = _args[0];
lean_object* v___x_645_ = _args[1];
lean_object* v___x_646_ = _args[2];
lean_object* v___f_647_ = _args[3];
lean_object* v___x_648_ = _args[4];
lean_object* v___x_649_ = _args[5];
lean_object* v___x_650_ = _args[6];
lean_object* v___x_651_ = _args[7];
lean_object* v_____r_652_ = _args[8];
lean_object* v_fields_653_ = _args[9];
lean_object* v___y_654_ = _args[10];
lean_object* v___y_655_ = _args[11];
lean_object* v___y_656_ = _args[12];
lean_object* v___y_657_ = _args[13];
lean_object* v___y_658_ = _args[14];
lean_object* v___y_659_ = _args[15];
lean_object* v___y_660_ = _args[16];
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___x_644_, v___x_645_, v___x_646_, v___f_647_, v___x_648_, v___x_649_, v___x_650_, v___x_651_, v_____r_652_, v_fields_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec_ref(v___x_644_);
return v_res_661_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_ref_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_ref_669_ = lean_ctor_get(v___y_666_, 2);
v___x_670_ = 0;
v___x_671_ = l_Lean_SourceInfo_fromRef(v_ref_669_, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_662_ = stack[0].m_obj;
lean_object* v___y_663_ = stack[1].m_obj;
lean_object* v___y_664_ = stack[2].m_obj;
lean_object* v___y_665_ = stack[3].m_obj;
lean_object* v___y_666_ = stack[4].m_obj;
lean_object* v___y_667_ = stack[5].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed(lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_681_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2));
v___x_686_ = l_String_toRawSubstring_x27(v___x_685_);
return v___x_686_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object* v_upperBound_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_xs_709_, lean_object* v___x_710_, lean_object* v_a_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___y_721_; uint8_t v___x_743_; 
v___x_743_ = lean_nat_dec_lt(v_a_711_, v_upperBound_706_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_a_711_);
lean_dec(v___x_710_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_b_712_);
return v___x_744_;
}
else
{
lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___f_745_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0));
v___x_746_ = l_Lean_instInhabitedExpr;
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_fget_borrowed(v___x_707_, v_a_711_);
lean_inc(v___x_748_);
v___x_749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_748_, v___x_743_);
v___x_750_ = lean_box(2);
lean_inc_ref(v___x_749_);
v___x_751_ = l_Lean_Syntax_mkStrLit(v___x_749_, v___x_750_);
v___x_752_ = lean_nat_add(v___x_708_, v_a_711_);
v___x_753_ = lean_array_get_borrowed(v___x_746_, v_xs_709_, v___x_752_);
lean_dec(v___x_752_);
v___x_754_ = lean_nat_dec_eq(v_a_711_, v___x_747_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
v___x_755_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_toCold_756_; lean_object* v_a_757_; lean_object* v_quotContext_758_; lean_object* v_currMacroScope_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_toCold_756_ = lean_ctor_get(v___y_717_, 0);
v_a_757_ = lean_ctor_get(v___x_755_, 0);
lean_inc_n(v_a_757_, 6);
lean_dec_ref_known(v___x_755_, 1);
v_quotContext_758_ = lean_ctor_get(v_toCold_756_, 8);
v_currMacroScope_759_ = lean_ctor_get(v_toCold_756_, 9);
v___x_760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_757_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v_a_757_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v_a_757_, v___x_763_, v___x_765_);
lean_inc_ref(v___x_762_);
v___x_767_ = l_Lean_Syntax_node3(v_a_757_, v___x_760_, v_b_712_, v___x_762_, v___x_766_);
v___x_768_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_759_);
lean_inc(v_quotContext_758_);
v___x_770_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_769_, v_currMacroScope_759_);
v___x_771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_772_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_772_, 0, v_a_757_);
lean_ctor_set(v___x_772_, 1, v___x_768_);
lean_ctor_set(v___x_772_, 2, v___x_770_);
lean_ctor_set(v___x_772_, 3, v___x_771_);
v___x_773_ = l_Lean_Syntax_node3(v_a_757_, v___x_760_, v___x_767_, v___x_762_, v___x_772_);
v___x_774_ = lean_box(0);
lean_inc(v___x_753_);
lean_inc(v___x_710_);
lean_inc(v___x_748_);
v___x_775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___x_749_, v___x_747_, v___x_750_, v___f_745_, v___x_751_, v___x_748_, v___x_710_, v___x_753_, v___x_774_, v___x_773_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v___x_749_);
v___y_721_ = v___x_775_;
goto v___jp_720_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___x_751_);
lean_dec_ref(v___x_749_);
lean_dec(v_b_712_);
lean_dec(v_a_711_);
lean_dec(v___x_710_);
v_a_776_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_755_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_755_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_box(0);
lean_inc(v___x_753_);
lean_inc(v___x_710_);
lean_inc(v___x_748_);
v___x_785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___x_749_, v___x_747_, v___x_750_, v___f_745_, v___x_751_, v___x_748_, v___x_710_, v___x_753_, v___x_784_, v_b_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v___x_749_);
v___y_721_ = v___x_785_;
goto v___jp_720_;
}
}
v___jp_720_:
{
if (lean_obj_tag(v___y_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_734_; 
v_a_722_ = lean_ctor_get(v___y_721_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___y_721_);
if (v_isSharedCheck_734_ == 0)
{
v___x_724_ = v___y_721_;
v_isShared_725_ = v_isSharedCheck_734_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___y_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_734_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
if (lean_obj_tag(v_a_722_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; 
lean_dec(v_a_711_);
lean_dec(v___x_710_);
v_a_726_ = lean_ctor_get(v_a_722_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v_a_722_, 1);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v_a_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_del_object(v___x_724_);
v_a_730_ = lean_ctor_get(v_a_722_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v_a_722_, 1);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_a_711_, v___x_731_);
lean_dec(v_a_711_);
v_a_711_ = v___x_732_;
v_b_712_ = v_a_730_;
goto _start;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_a_711_);
lean_dec(v___x_710_);
v_a_735_ = lean_ctor_get(v___y_721_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___y_721_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___y_721_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___y_721_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_706_ = stack[0].m_obj;
lean_object* v___x_707_ = stack[1].m_obj;
lean_object* v___x_708_ = stack[2].m_obj;
lean_object* v_xs_709_ = stack[3].m_obj;
lean_object* v___x_710_ = stack[4].m_obj;
lean_object* v_a_711_ = stack[5].m_obj;
lean_object* v_b_712_ = stack[6].m_obj;
lean_object* v___y_713_ = stack[7].m_obj;
lean_object* v___y_714_ = stack[8].m_obj;
lean_object* v___y_715_ = stack[9].m_obj;
lean_object* v___y_716_ = stack[10].m_obj;
lean_object* v___y_717_ = stack[11].m_obj;
lean_object* v___y_718_ = stack[12].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_706_, v___x_707_, v___x_708_, v_xs_709_, v___x_710_, v_a_711_, v_b_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object* v_upperBound_787_, lean_object* v___x_788_, lean_object* v___x_789_, lean_object* v_xs_790_, lean_object* v___x_791_, lean_object* v_a_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_787_, v___x_788_, v___x_789_, v_xs_790_, v___x_791_, v_a_792_, v_b_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_xs_790_);
lean_dec(v___x_789_);
lean_dec_ref(v___x_788_);
lean_dec(v_upperBound_787_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0));
v___x_804_ = l_String_toRawSubstring_x27(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9));
v___x_826_ = l_String_toRawSubstring_x27(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object* v___x_846_, lean_object* v_numParams_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v_xs_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_toCold_859_; lean_object* v_ref_860_; lean_object* v_quotContext_861_; lean_object* v_currMacroScope_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_toCold_859_ = lean_ctor_get(v___y_856_, 0);
v_ref_860_ = lean_ctor_get(v___y_856_, 2);
v_quotContext_861_ = lean_ctor_get(v_toCold_859_, 8);
v_currMacroScope_862_ = lean_ctor_get(v_toCold_859_, 9);
v___x_863_ = 0;
v___x_864_ = l_Lean_SourceInfo_fromRef(v_ref_860_, v___x_863_);
v___x_865_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3));
lean_inc(v_currMacroScope_862_);
lean_inc(v_quotContext_861_);
v___x_867_ = l_Lean_addMacroScope(v_quotContext_861_, v___x_866_, v_currMacroScope_862_);
v___x_868_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8));
v___x_869_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_869_, 0, v___x_864_);
lean_ctor_set(v___x_869_, 1, v___x_865_);
lean_ctor_set(v___x_869_, 2, v___x_867_);
lean_ctor_set(v___x_869_, 3, v___x_868_);
v___x_908_ = lean_array_get_size(v_xs_850_);
v___x_909_ = lean_array_get_size(v___x_846_);
v___x_910_ = lean_nat_add(v_numParams_847_, v___x_909_);
v___x_911_ = lean_nat_dec_eq(v___x_908_, v___x_910_);
lean_dec(v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref_known(v___x_869_, 4);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
v___x_912_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19);
v___x_913_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_912_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
v___y_871_ = v___y_852_;
v___y_872_ = v___y_853_;
v___y_873_ = v___y_854_;
v___y_874_ = v___y_855_;
v___y_875_ = v___y_856_;
v___y_876_ = v___y_857_;
goto v___jp_870_;
}
v___jp_870_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_array_get_size(v___x_846_);
v___x_878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v___x_877_, v___x_846_, v_numParams_847_, v_xs_850_, v___x_848_, v___x_849_, v___x_869_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_toCold_879_; lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_907_; 
v_toCold_879_ = lean_ctor_get(v___y_875_, 0);
v_a_880_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_907_ == 0)
{
v___x_882_ = v___x_878_;
v_isShared_883_ = v_isSharedCheck_907_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_907_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_ref_884_; lean_object* v_quotContext_885_; lean_object* v_currMacroScope_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v_ref_884_ = lean_ctor_get(v___y_875_, 2);
v_quotContext_885_ = lean_ctor_get(v_toCold_879_, 8);
v_currMacroScope_886_ = lean_ctor_get(v_toCold_879_, 9);
v___x_887_ = l_Lean_SourceInfo_fromRef(v_ref_884_, v___x_863_);
v___x_888_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31));
v___x_889_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10);
v___x_890_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12));
lean_inc(v_currMacroScope_886_);
lean_inc(v_quotContext_885_);
v___x_891_ = l_Lean_addMacroScope(v_quotContext_885_, v___x_890_, v_currMacroScope_886_);
v___x_892_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15));
lean_inc_n(v___x_887_, 6);
v___x_893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_893_, 0, v___x_887_);
lean_ctor_set(v___x_893_, 1, v___x_889_);
lean_ctor_set(v___x_893_, 2, v___x_891_);
lean_ctor_set(v___x_893_, 3, v___x_892_);
v___x_894_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_895_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_896_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16));
v___x_897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_887_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_Syntax_node1(v___x_887_, v___x_895_, v___x_897_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17));
v___x_900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_887_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_Syntax_node1(v___x_887_, v___x_895_, v___x_900_);
v___x_902_ = l_Lean_Syntax_node3(v___x_887_, v___x_894_, v___x_898_, v_a_880_, v___x_901_);
v___x_903_ = l_Lean_Syntax_node2(v___x_887_, v___x_888_, v___x_893_, v___x_902_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_903_);
v___x_905_ = v___x_882_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_846_ = stack[0].m_obj;
lean_object* v_numParams_847_ = stack[1].m_obj;
lean_object* v___x_848_ = stack[2].m_obj;
lean_object* v___x_849_ = stack[3].m_obj;
lean_object* v_xs_850_ = stack[4].m_obj;
lean_object* v_x_851_ = stack[5].m_obj;
lean_object* v___y_852_ = stack[6].m_obj;
lean_object* v___y_853_ = stack[7].m_obj;
lean_object* v___y_854_ = stack[8].m_obj;
lean_object* v___y_855_ = stack[9].m_obj;
lean_object* v___y_856_ = stack[10].m_obj;
lean_object* v___y_857_ = stack[11].m_obj;
lean_object* v_res_922_;
v_res_922_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(v___x_846_, v_numParams_847_, v___x_848_, v___x_849_, v_xs_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object* v___x_923_, lean_object* v_numParams_924_, lean_object* v___x_925_, lean_object* v___x_926_, lean_object* v_xs_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(v___x_923_, v_numParams_924_, v___x_925_, v___x_926_, v_xs_927_, v_x_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_x_928_);
lean_dec_ref(v_xs_927_);
lean_dec(v_numParams_924_);
lean_dec_ref(v___x_923_);
return v_res_936_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_instMonadEIO___redArg();
return v___x_937_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object* v_msg_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_toApplicative_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1045_; 
v___x_952_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0);
v___x_953_ = l_StateRefT_x27_instMonad___redArg(v___x_952_);
v_toApplicative_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v___x_953_, 1);
lean_dec(v_unused_1046_);
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_1045_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_toApplicative_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1045_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_toFunctor_958_; lean_object* v_toSeq_959_; lean_object* v_toSeqLeft_960_; lean_object* v_toSeqRight_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1043_; 
v_toFunctor_958_ = lean_ctor_get(v_toApplicative_954_, 0);
v_toSeq_959_ = lean_ctor_get(v_toApplicative_954_, 2);
v_toSeqLeft_960_ = lean_ctor_get(v_toApplicative_954_, 3);
v_toSeqRight_961_ = lean_ctor_get(v_toApplicative_954_, 4);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_toApplicative_954_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_toApplicative_954_, 1);
lean_dec(v_unused_1044_);
v___x_963_ = v_toApplicative_954_;
v_isShared_964_ = v_isSharedCheck_1043_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_toSeqRight_961_);
lean_inc(v_toSeqLeft_960_);
lean_inc(v_toSeq_959_);
lean_inc(v_toFunctor_958_);
lean_dec(v_toApplicative_954_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1043_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___x_974_; 
v___f_965_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1));
v___f_966_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_958_);
v___f_967_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_967_, 0, v_toFunctor_958_);
v___f_968_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_968_, 0, v_toFunctor_958_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___f_967_);
lean_ctor_set(v___x_969_, 1, v___f_968_);
v___f_970_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_970_, 0, v_toSeqRight_961_);
v___f_971_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_971_, 0, v_toSeqLeft_960_);
v___f_972_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_972_, 0, v_toSeq_959_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 4, v___f_970_);
lean_ctor_set(v___x_963_, 3, v___f_971_);
lean_ctor_set(v___x_963_, 2, v___f_972_);
lean_ctor_set(v___x_963_, 1, v___f_965_);
lean_ctor_set(v___x_963_, 0, v___x_969_);
v___x_974_ = v___x_963_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___f_965_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___f_972_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v___f_971_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___f_970_);
v___x_974_ = v_reuseFailAlloc_1042_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___f_966_);
lean_ctor_set(v___x_956_, 0, v___x_974_);
v___x_976_ = v___x_956_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___f_966_);
v___x_976_ = v_reuseFailAlloc_1041_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v_toApplicative_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1039_; 
v___x_977_ = l_StateRefT_x27_instMonad___redArg(v___x_976_);
v_toApplicative_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_977_, 1);
lean_dec(v_unused_1040_);
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1039_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_toApplicative_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1039_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_toFunctor_982_; lean_object* v_toSeq_983_; lean_object* v_toSeqLeft_984_; lean_object* v_toSeqRight_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1037_; 
v_toFunctor_982_ = lean_ctor_get(v_toApplicative_978_, 0);
v_toSeq_983_ = lean_ctor_get(v_toApplicative_978_, 2);
v_toSeqLeft_984_ = lean_ctor_get(v_toApplicative_978_, 3);
v_toSeqRight_985_ = lean_ctor_get(v_toApplicative_978_, 4);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_toApplicative_978_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_toApplicative_978_, 1);
lean_dec(v_unused_1038_);
v___x_987_ = v_toApplicative_978_;
v_isShared_988_ = v_isSharedCheck_1037_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_toSeqRight_985_);
lean_inc(v_toSeqLeft_984_);
lean_inc(v_toSeq_983_);
lean_inc(v_toFunctor_982_);
lean_dec(v_toApplicative_978_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1037_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_998_; 
v___f_989_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3));
v___f_990_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_982_);
v___f_991_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_991_, 0, v_toFunctor_982_);
v___f_992_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_992_, 0, v_toFunctor_982_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___f_991_);
lean_ctor_set(v___x_993_, 1, v___f_992_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_994_, 0, v_toSeqRight_985_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_995_, 0, v_toSeqLeft_984_);
v___f_996_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_996_, 0, v_toSeq_983_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v___f_994_);
lean_ctor_set(v___x_987_, 3, v___f_995_);
lean_ctor_set(v___x_987_, 2, v___f_996_);
lean_ctor_set(v___x_987_, 1, v___f_989_);
lean_ctor_set(v___x_987_, 0, v___x_993_);
v___x_998_ = v___x_987_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___f_989_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v___f_996_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v___f_995_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v___f_994_);
v___x_998_ = v_reuseFailAlloc_1036_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___f_990_);
lean_ctor_set(v___x_980_, 0, v___x_998_);
v___x_1000_ = v___x_980_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___f_990_);
v___x_1000_ = v_reuseFailAlloc_1035_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v_toApplicative_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1033_; 
v___x_1001_ = l_StateRefT_x27_instMonad___redArg(v___x_1000_);
v_toApplicative_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v___x_1001_, 1);
lean_dec(v_unused_1034_);
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1033_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_toApplicative_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1033_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_toFunctor_1006_; lean_object* v_toSeq_1007_; lean_object* v_toSeqLeft_1008_; lean_object* v_toSeqRight_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1031_; 
v_toFunctor_1006_ = lean_ctor_get(v_toApplicative_1002_, 0);
v_toSeq_1007_ = lean_ctor_get(v_toApplicative_1002_, 2);
v_toSeqLeft_1008_ = lean_ctor_get(v_toApplicative_1002_, 3);
v_toSeqRight_1009_ = lean_ctor_get(v_toApplicative_1002_, 4);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_toApplicative_1002_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_toApplicative_1002_, 1);
lean_dec(v_unused_1032_);
v___x_1011_ = v_toApplicative_1002_;
v_isShared_1012_ = v_isSharedCheck_1031_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_toSeqRight_1009_);
lean_inc(v_toSeqLeft_1008_);
lean_inc(v_toSeq_1007_);
lean_inc(v_toFunctor_1006_);
lean_dec(v_toApplicative_1002_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1031_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___x_1022_; 
v___f_1013_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5));
v___f_1014_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6));
lean_inc_ref(v_toFunctor_1006_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toFunctor_1006_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toFunctor_1006_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___f_1015_);
lean_ctor_set(v___x_1017_, 1, v___f_1016_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeqRight_1009_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toSeqLeft_1008_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toSeq_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 4, v___f_1018_);
lean_ctor_set(v___x_1011_, 3, v___f_1019_);
lean_ctor_set(v___x_1011_, 2, v___f_1020_);
lean_ctor_set(v___x_1011_, 1, v___f_1013_);
lean_ctor_set(v___x_1011_, 0, v___x_1017_);
v___x_1022_ = v___x_1011_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v___f_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v___f_1018_);
v___x_1022_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___f_1014_);
lean_ctor_set(v___x_1004_, 0, v___x_1022_);
v___x_1024_ = v___x_1004_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___f_1014_);
v___x_1024_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_19115__overap_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = l_instInhabitedOfMonad___redArg(v___x_1024_, v___x_1025_);
v___x_19115__overap_1027_ = lean_panic_fn_borrowed(v___x_1026_, v_msg_944_);
lean_dec(v___x_1026_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
v___x_1028_ = lean_apply_7(v___x_19115__overap_1027_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, lean_box(0));
return v___x_1028_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_944_ = stack[0].m_obj;
lean_object* v___y_945_ = stack[1].m_obj;
lean_object* v___y_946_ = stack[2].m_obj;
lean_object* v___y_947_ = stack[3].m_obj;
lean_object* v___y_948_ = stack[4].m_obj;
lean_object* v___y_949_ = stack[5].m_obj;
lean_object* v___y_950_ = stack[6].m_obj;
lean_object* v_res_1047_;
v_res_1047_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v_msg_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object* v_msg_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v_msg_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1066_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6));
v___x_1067_ = lean_unsigned_to_nat(11u);
v___x_1068_ = lean_unsigned_to_nat(122u);
v___x_1069_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5));
v___x_1070_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4));
v___x_1071_ = l_mkPanicMessageWithDecl(v___x_1070_, v___x_1069_, v___x_1068_, v___x_1067_, v___x_1066_);
return v___x_1071_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object* v_constName_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1088_; lean_object* v_env_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_st_ref_get(v___y_1078_);
v_env_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_env_1089_);
lean_dec(v___x_1088_);
v___x_1090_ = 0;
lean_inc(v_constName_1072_);
v___x_1091_ = l_Lean_Environment_findAsync_x3f(v_env_1089_, v_constName_1072_, v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 1)
{
lean_object* v_val_1092_; uint8_t v_kind_1093_; 
v_val_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_val_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v_kind_1093_ = lean_ctor_get_uint8(v_val_1092_, sizeof(void*)*3);
if (v_kind_1093_ == 6)
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1092_);
if (lean_obj_tag(v___x_1094_) == 6)
{
lean_object* v_val_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_constName_1072_);
v_val_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_val_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 0);
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_val_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v___x_1094_);
v___x_1103_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7);
v___x_1104_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v___x_1103_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
if (lean_obj_tag(v_a_1105_) == 0)
{
lean_del_object(v___x_1107_);
goto v___jp_1080_;
}
else
{
lean_object* v_val_1109_; lean_object* v___x_1111_; 
lean_dec(v_constName_1072_);
v_val_1109_ = lean_ctor_get(v_a_1105_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v_a_1105_, 1);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v_val_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_val_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_constName_1072_);
v_a_1114_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1104_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1104_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_dec(v_val_1092_);
goto v___jp_1080_;
}
}
else
{
lean_dec(v___x_1091_);
goto v___jp_1080_;
}
v___jp_1080_:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1081_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1);
v___x_1082_ = 0;
v___x_1083_ = l_Lean_MessageData_ofConstName(v_constName_1072_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_1086_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1087_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1072_ = stack[0].m_obj;
lean_object* v___y_1073_ = stack[1].m_obj;
lean_object* v___y_1074_ = stack[2].m_obj;
lean_object* v___y_1075_ = stack[3].m_obj;
lean_object* v___y_1076_ = stack[4].m_obj;
lean_object* v___y_1077_ = stack[5].m_obj;
lean_object* v___y_1078_ = stack[6].m_obj;
lean_object* v_res_1122_;
v_res_1122_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_constName_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1122_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object* v_constName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_constName_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1131_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object* v_header_1132_, lean_object* v_indVal_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_toConstantVal_1141_; lean_object* v_numParams_1142_; lean_object* v_ctors_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_toConstantVal_1141_ = lean_ctor_get(v_indVal_1133_, 0);
lean_inc_ref(v_toConstantVal_1141_);
v_numParams_1142_ = lean_ctor_get(v_indVal_1133_, 1);
lean_inc(v_numParams_1142_);
v_ctors_1143_ = lean_ctor_get(v_indVal_1133_, 4);
lean_inc(v_ctors_1143_);
lean_dec_ref(v_indVal_1133_);
v___x_1144_ = lean_box(0);
v___x_1145_ = l_List_head_x21___redArg(v___x_1144_, v_ctors_1143_);
lean_dec(v_ctors_1143_);
v___x_1146_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v___x_1145_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v_toConstantVal_1149_; lean_object* v_env_1150_; lean_object* v_name_1151_; lean_object* v_targetNames_1152_; lean_object* v_type_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___f_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = lean_st_ref_get(v_a_1139_);
v_toConstantVal_1149_ = lean_ctor_get(v_a_1147_, 0);
lean_inc_ref(v_toConstantVal_1149_);
lean_dec(v_a_1147_);
v_env_1150_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_ref(v_env_1150_);
lean_dec(v___x_1148_);
v_name_1151_ = lean_ctor_get(v_toConstantVal_1141_, 0);
lean_inc(v_name_1151_);
lean_dec_ref(v_toConstantVal_1141_);
v_targetNames_1152_ = lean_ctor_get(v_header_1132_, 2);
v_type_1153_ = lean_ctor_get(v_toConstantVal_1149_, 2);
lean_inc_ref(v_type_1153_);
lean_dec_ref(v_toConstantVal_1149_);
v___x_1154_ = l_Lean_getStructureFields(v_env_1150_, v_name_1151_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_array_get_borrowed(v___x_1144_, v_targetNames_1152_, v___x_1155_);
lean_inc(v___x_1156_);
v___x_1157_ = l_Lean_mkIdent(v___x_1156_);
v___f_1158_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1158_, 0, v___x_1154_);
lean_closure_set(v___f_1158_, 1, v_numParams_1142_);
lean_closure_set(v___f_1158_, 2, v___x_1157_);
lean_closure_set(v___f_1158_, 3, v___x_1155_);
v___x_1159_ = 0;
v___x_1160_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_1153_, v___f_1158_, v___x_1159_, v___x_1159_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1160_;
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v_numParams_1142_);
lean_dec_ref(v_toConstantVal_1141_);
v_a_1161_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1146_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1146_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkBodyForStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_1132_ = stack[0].m_obj;
lean_object* v_indVal_1133_ = stack[1].m_obj;
lean_object* v_a_1134_ = stack[2].m_obj;
lean_object* v_a_1135_ = stack[3].m_obj;
lean_object* v_a_1136_ = stack[4].m_obj;
lean_object* v_a_1137_ = stack[5].m_obj;
lean_object* v_a_1138_ = stack[6].m_obj;
lean_object* v_a_1139_ = stack[7].m_obj;
lean_object* v_res_1169_;
v_res_1169_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_1132_, v_indVal_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
stack->m_obj
 = v_res_1169_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object* v_header_1170_, lean_object* v_indVal_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_1170_, v_indVal_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec_ref(v_header_1170_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object* v___x_1180_, lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v_inst_1183_, lean_object* v_R_1184_, lean_object* v_a_1185_, lean_object* v_b_1186_, lean_object* v_c_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_1180_, v___x_1182_, v_a_1185_, v_b_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object* v___x_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_inst_1192_, lean_object* v_R_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_, lean_object* v_c_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(v___x_1189_, v___x_1190_, v___x_1191_, v_inst_1192_, v_R_1193_, v_a_1194_, v_b_1195_, v_c_1196_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
lean_dec(v___x_1189_);
return v_res_1197_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object* v_upperBound_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v_xs_1201_, lean_object* v___x_1202_, lean_object* v_inst_1203_, lean_object* v_R_1204_, lean_object* v_a_1205_, lean_object* v_b_1206_, lean_object* v_c_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_1198_, v___x_1199_, v___x_1200_, v_xs_1201_, v___x_1202_, v_a_1205_, v_b_1206_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1198_ = stack[0].m_obj;
lean_object* v___x_1199_ = stack[1].m_obj;
lean_object* v___x_1200_ = stack[2].m_obj;
lean_object* v_xs_1201_ = stack[3].m_obj;
lean_object* v___x_1202_ = stack[4].m_obj;
lean_object* v_a_1205_ = stack[7].m_obj;
lean_object* v_b_1206_ = stack[8].m_obj;
lean_object* v___y_1208_ = stack[10].m_obj;
lean_object* v___y_1209_ = stack[11].m_obj;
lean_object* v___y_1210_ = stack[12].m_obj;
lean_object* v___y_1211_ = stack[13].m_obj;
lean_object* v___y_1212_ = stack[14].m_obj;
lean_object* v___y_1213_ = stack[15].m_obj;
lean_object* v_res_1216_;
v_res_1216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(v_upperBound_1198_, v___x_1199_, v___x_1200_, v_xs_1201_, v___x_1202_, lean_box(0), lean_box(0), v_a_1205_, v_b_1206_, lean_box(0), v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
stack->m_obj
 = v_res_1216_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_1217_ = _args[0];
lean_object* v___x_1218_ = _args[1];
lean_object* v___x_1219_ = _args[2];
lean_object* v_xs_1220_ = _args[3];
lean_object* v___x_1221_ = _args[4];
lean_object* v_inst_1222_ = _args[5];
lean_object* v_R_1223_ = _args[6];
lean_object* v_a_1224_ = _args[7];
lean_object* v_b_1225_ = _args[8];
lean_object* v_c_1226_ = _args[9];
lean_object* v___y_1227_ = _args[10];
lean_object* v___y_1228_ = _args[11];
lean_object* v___y_1229_ = _args[12];
lean_object* v___y_1230_ = _args[13];
lean_object* v___y_1231_ = _args[14];
lean_object* v___y_1232_ = _args[15];
lean_object* v___y_1233_ = _args[16];
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(v_upperBound_1217_, v___x_1218_, v___x_1219_, v_xs_1220_, v___x_1221_, v_inst_1222_, v_R_1223_, v_a_1224_, v_b_1225_, v_c_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v_xs_1220_);
lean_dec(v___x_1219_);
lean_dec_ref(v___x_1218_);
lean_dec(v_upperBound_1217_);
return v_res_1234_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object* v_00_u03b1_1235_, lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1236_ = stack[1].m_obj;
lean_object* v___y_1237_ = stack[2].m_obj;
lean_object* v___y_1238_ = stack[3].m_obj;
lean_object* v___y_1239_ = stack[4].m_obj;
lean_object* v___y_1240_ = stack[5].m_obj;
lean_object* v___y_1241_ = stack[6].m_obj;
lean_object* v___y_1242_ = stack[7].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_box(0), v_msg_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(v_00_u03b1_1246_, v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1255_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(lean_object* v_msgData_1256_, lean_object* v_macroStack_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_1256_, v_macroStack_1257_, v___y_1262_);
return v___x_1265_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1256_ = stack[0].m_obj;
lean_object* v_macroStack_1257_ = stack[1].m_obj;
lean_object* v___y_1258_ = stack[2].m_obj;
lean_object* v___y_1259_ = stack[3].m_obj;
lean_object* v___y_1260_ = stack[4].m_obj;
lean_object* v___y_1261_ = stack[5].m_obj;
lean_object* v___y_1262_ = stack[6].m_obj;
lean_object* v___y_1263_ = stack[7].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(v_msgData_1256_, v_macroStack_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___boxed(lean_object* v_msgData_1267_, lean_object* v_macroStack_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(v_msgData_1267_, v_macroStack_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1276_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object* v_upperBound_1284_, lean_object* v_a_1285_, lean_object* v_b_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_nat_dec_lt(v_a_1285_, v_upperBound_1284_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_a_1285_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_b_1286_);
return v___x_1290_;
}
else
{
lean_object* v_ref_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_ref_1291_ = lean_ctor_get(v___y_1287_, 2);
v___x_1292_ = 0;
v___x_1293_ = l_Lean_SourceInfo_fromRef(v_ref_1291_, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
lean_inc(v___x_1293_);
v___x_1296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1293_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_node1(v___x_1293_, v___x_1294_, v___x_1296_);
v___x_1298_ = lean_array_push(v_b_1286_, v___x_1297_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_a_1285_, v___x_1299_);
lean_dec(v_a_1285_);
v_a_1285_ = v___x_1300_;
v_b_1286_ = v___x_1298_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1284_ = stack[0].m_obj;
lean_object* v_a_1285_ = stack[1].m_obj;
lean_object* v_b_1286_ = stack[2].m_obj;
lean_object* v___y_1287_ = stack[3].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1284_, v_a_1285_, v_b_1286_, v___y_1287_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_1303_, lean_object* v_a_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1303_, v_a_1304_, v_b_1305_, v___y_1306_);
lean_dec_ref(v___y_1306_);
lean_dec(v_upperBound_1303_);
return v_res_1308_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t v_sz_1309_, size_t v_i_1310_, lean_object* v_bs_1311_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1310_, v_sz_1309_);
if (v___x_1312_ == 0)
{
return v_bs_1311_;
}
else
{
lean_object* v_v_1313_; lean_object* v___x_1314_; lean_object* v_bs_x27_1315_; size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v_v_1313_ = lean_array_uget(v_bs_1311_, v_i_1310_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v_bs_x27_1315_ = lean_array_uset(v_bs_1311_, v_i_1310_, v___x_1314_);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_add(v_i_1310_, v___x_1316_);
v___x_1318_ = lean_array_uset(v_bs_x27_1315_, v_i_1310_, v_v_1313_);
v_i_1310_ = v___x_1317_;
v_bs_1311_ = v___x_1318_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1309_ = stack[0].m_num;
size_t v_i_1310_ = stack[1].m_num;
lean_object* v_bs_1311_ = stack[2].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_1309_, v_i_1310_, v_bs_1311_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_sz_1321_, lean_object* v_i_1322_, lean_object* v_bs_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1321_);
lean_dec(v_sz_1321_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1322_);
lean_dec(v_i_1322_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_boxed_1324_, v_i_boxed_1325_, v_bs_1323_);
return v_res_1326_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0));
v___x_1329_ = l_String_toRawSubstring_x27(v___x_1328_);
return v___x_1329_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object* v___f_1342_, lean_object* v_snd_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_toConstantVal_1346_, lean_object* v_auxFunName_1347_, lean_object* v_____r_1348_, lean_object* v_ctorArgs_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___y_1358_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = l_Lean_Expr_fvarId_x21(v___x_1345_);
v___x_1447_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_1446_, v___y_1352_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1516_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1516_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1516_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
v___x_1453_ = l_Lean_BinderInfo_isExplicit(v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_dec(v_auxFunName_1347_);
lean_dec_ref(v___x_1345_);
lean_dec(v___x_1344_);
lean_dec_ref(v___f_1342_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_ctorArgs_1349_);
lean_ctor_set(v___x_1454_, 1, v_snd_1343_);
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1455_);
v___x_1457_ = v___x_1450_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v___x_1459_; 
lean_del_object(v___x_1450_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc_ref(v___x_1345_);
v___x_1459_ = lean_infer_type(v___x_1345_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v_name_1461_; uint8_t v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v_name_1461_ = lean_ctor_get(v_toConstantVal_1346_, 0);
v___x_1462_ = l_Lean_Expr_isAppOf(v_a_1460_, v_name_1461_);
lean_dec(v_a_1460_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_auxFunName_1347_);
lean_inc_ref(v___x_1345_);
v___x_1463_ = l_Lean_Meta_isType(v___x_1345_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; uint8_t v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v___x_1465_ = lean_unbox(v_a_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
lean_dec_ref_known(v___x_1463_, 1);
v___x_1466_ = l_Lean_Meta_isProof(v___x_1345_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1358_ = v___x_1466_;
goto v___jp_1357_;
}
else
{
lean_dec_ref(v___x_1345_);
v___y_1358_ = v___x_1463_;
goto v___jp_1357_;
}
}
else
{
lean_dec_ref(v___x_1345_);
v___y_1358_ = v___x_1463_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1467_; 
lean_dec_ref(v___x_1345_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1467_ = lean_apply_7(v___f_1342_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_toCold_1468_; lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1499_; 
v_toCold_1468_ = lean_ctor_get(v___y_1354_, 0);
v_a_1469_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1499_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1499_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_quotContext_1473_; lean_object* v_currMacroScope_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v_quotContext_1473_ = lean_ctor_get(v_toCold_1468_, 8);
v_currMacroScope_1474_ = lean_ctor_get(v_toCold_1468_, 9);
v___x_1475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_1476_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_1469_, 7);
v___x_1477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1469_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1479_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_1474_);
lean_inc(v_quotContext_1473_);
v___x_1480_ = l_Lean_addMacroScope(v_quotContext_1473_, v___x_1479_, v_currMacroScope_1474_);
v___x_1481_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1469_);
lean_ctor_set(v___x_1482_, 1, v___x_1478_);
lean_ctor_set(v___x_1482_, 2, v___x_1480_);
lean_ctor_set(v___x_1482_, 3, v___x_1481_);
lean_inc_ref(v___x_1477_);
v___x_1483_ = l_Lean_Syntax_node3(v_a_1469_, v___x_1475_, v_snd_1343_, v___x_1477_, v___x_1482_);
v___x_1484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31));
v___x_1485_ = l_Lean_mkIdent(v_auxFunName_1347_);
v___x_1486_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1487_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1488_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1469_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_Syntax_node1(v_a_1469_, v___x_1487_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_node2(v_a_1469_, v___x_1486_, v___x_1344_, v___x_1490_);
v___x_1492_ = l_Lean_Syntax_node2(v_a_1469_, v___x_1484_, v___x_1485_, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_node3(v_a_1469_, v___x_1475_, v___x_1483_, v___x_1477_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_ctorArgs_1349_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1495_);
v___x_1497_ = v___x_1471_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v_ctorArgs_1349_);
lean_dec(v_auxFunName_1347_);
lean_dec(v___x_1344_);
lean_dec(v_snd_1343_);
v_a_1500_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1467_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1467_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_ctorArgs_1349_);
lean_dec(v_auxFunName_1347_);
lean_dec_ref(v___x_1345_);
lean_dec(v___x_1344_);
lean_dec(v_snd_1343_);
lean_dec_ref(v___f_1342_);
v_a_1508_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1459_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1459_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_ctorArgs_1349_);
lean_dec(v_auxFunName_1347_);
lean_dec_ref(v___x_1345_);
lean_dec(v___x_1344_);
lean_dec(v_snd_1343_);
lean_dec_ref(v___f_1342_);
v_a_1517_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1447_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1447_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
v___jp_1357_:
{
if (lean_obj_tag(v___y_1358_) == 0)
{
lean_object* v_a_1359_; uint8_t v___x_1360_; 
v_a_1359_ = lean_ctor_get(v___y_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___y_1358_, 1);
v___x_1360_ = lean_unbox(v_a_1359_);
lean_dec(v_a_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1361_ = lean_apply_7(v___f_1342_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_toCold_1362_; lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1393_; 
v_toCold_1362_ = lean_ctor_get(v___y_1354_, 0);
v_a_1363_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1393_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1393_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_quotContext_1367_; lean_object* v_currMacroScope_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v_quotContext_1367_ = lean_ctor_get(v_toCold_1362_, 8);
v_currMacroScope_1368_ = lean_ctor_get(v_toCold_1362_, 9);
v___x_1369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_1370_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_1363_, 6);
v___x_1371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1363_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1373_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc_n(v_currMacroScope_1368_, 2);
lean_inc_n(v_quotContext_1367_, 2);
v___x_1374_ = l_Lean_addMacroScope(v_quotContext_1367_, v___x_1373_, v_currMacroScope_1368_);
v___x_1375_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1376_, 0, v_a_1363_);
lean_ctor_set(v___x_1376_, 1, v___x_1372_);
lean_ctor_set(v___x_1376_, 2, v___x_1374_);
lean_ctor_set(v___x_1376_, 3, v___x_1375_);
lean_inc_ref(v___x_1371_);
v___x_1377_ = l_Lean_Syntax_node3(v_a_1363_, v___x_1369_, v_snd_1343_, v___x_1371_, v___x_1376_);
v___x_1378_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31));
v___x_1379_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1);
v___x_1380_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2));
v___x_1381_ = l_Lean_addMacroScope(v_quotContext_1367_, v___x_1380_, v_currMacroScope_1368_);
v___x_1382_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4));
v___x_1383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1363_);
lean_ctor_set(v___x_1383_, 1, v___x_1379_);
lean_ctor_set(v___x_1383_, 2, v___x_1381_);
lean_ctor_set(v___x_1383_, 3, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1385_ = l_Lean_Syntax_node1(v_a_1363_, v___x_1384_, v___x_1344_);
v___x_1386_ = l_Lean_Syntax_node2(v_a_1363_, v___x_1378_, v___x_1383_, v___x_1385_);
v___x_1387_ = l_Lean_Syntax_node3(v_a_1363_, v___x_1369_, v___x_1377_, v___x_1371_, v___x_1386_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_ctorArgs_1349_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1389_);
v___x_1391_ = v___x_1365_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_ctorArgs_1349_);
lean_dec(v___x_1344_);
lean_dec(v_snd_1343_);
v_a_1394_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1361_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1361_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v___x_1402_; 
lean_dec(v___x_1344_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1402_ = lean_apply_7(v___f_1342_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, lean_box(0));
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_toCold_1403_; lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1429_; 
v_toCold_1403_ = lean_ctor_get(v___y_1354_, 0);
v_a_1404_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1406_ = v___x_1402_;
v_isShared_1407_ = v_isSharedCheck_1429_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1429_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_quotContext_1408_; lean_object* v_currMacroScope_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v_quotContext_1408_ = lean_ctor_get(v_toCold_1403_, 8);
v_currMacroScope_1409_ = lean_ctor_get(v_toCold_1403_, 9);
v___x_1410_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1));
v___x_1411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2));
lean_inc_n(v_a_1404_, 5);
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_a_1404_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_1409_);
lean_inc(v_quotContext_1408_);
v___x_1415_ = l_Lean_addMacroScope(v_quotContext_1408_, v___x_1414_, v_currMacroScope_1409_);
v___x_1416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1417_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1417_, 0, v_a_1404_);
lean_ctor_set(v___x_1417_, 1, v___x_1413_);
lean_ctor_set(v___x_1417_, 2, v___x_1415_);
lean_ctor_set(v___x_1417_, 3, v___x_1416_);
lean_inc_ref(v___x_1412_);
v___x_1418_ = l_Lean_Syntax_node3(v_a_1404_, v___x_1410_, v_snd_1343_, v___x_1412_, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_1420_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59));
v___x_1421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_a_1404_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = l_Lean_Syntax_node1(v_a_1404_, v___x_1419_, v___x_1421_);
v___x_1423_ = l_Lean_Syntax_node3(v_a_1404_, v___x_1410_, v___x_1418_, v___x_1412_, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_ctorArgs_1349_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1425_);
v___x_1427_ = v___x_1406_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_ctorArgs_1349_);
lean_dec(v_snd_1343_);
v_a_1430_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1402_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1402_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_ctorArgs_1349_);
lean_dec(v___x_1344_);
lean_dec(v_snd_1343_);
lean_dec_ref(v___f_1342_);
v_a_1438_ = lean_ctor_get(v___y_1358_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___y_1358_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___y_1358_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___y_1358_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1342_ = stack[0].m_obj;
lean_object* v_snd_1343_ = stack[1].m_obj;
lean_object* v___x_1344_ = stack[2].m_obj;
lean_object* v___x_1345_ = stack[3].m_obj;
lean_object* v_toConstantVal_1346_ = stack[4].m_obj;
lean_object* v_auxFunName_1347_ = stack[5].m_obj;
lean_object* v_____r_1348_ = stack[6].m_obj;
lean_object* v_ctorArgs_1349_ = stack[7].m_obj;
lean_object* v___y_1350_ = stack[8].m_obj;
lean_object* v___y_1351_ = stack[9].m_obj;
lean_object* v___y_1352_ = stack[10].m_obj;
lean_object* v___y_1353_ = stack[11].m_obj;
lean_object* v___y_1354_ = stack[12].m_obj;
lean_object* v___y_1355_ = stack[13].m_obj;
lean_object* v_res_1525_;
v_res_1525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1342_, v_snd_1343_, v___x_1344_, v___x_1345_, v_toConstantVal_1346_, v_auxFunName_1347_, v_____r_1348_, v_ctorArgs_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1525_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object* v___f_1526_, lean_object* v_snd_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_toConstantVal_1530_, lean_object* v_auxFunName_1531_, lean_object* v_____r_1532_, lean_object* v_ctorArgs_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1526_, v_snd_1527_, v___x_1528_, v___x_1529_, v_toConstantVal_1530_, v_auxFunName_1531_, v_____r_1532_, v_ctorArgs_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v_toConstantVal_1530_);
return v_res_1541_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object* v_upperBound_1545_, lean_object* v_xs_1546_, lean_object* v_indVal_1547_, lean_object* v_auxFunName_1548_, lean_object* v_header_1549_, lean_object* v_a_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___y_1560_; uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_lt(v_a_1550_, v_upperBound_1545_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec(v_a_1550_);
lean_dec(v_auxFunName_1548_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_b_1551_);
return v___x_1583_;
}
else
{
lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1633_; 
v_fst_1584_ = lean_ctor_get(v_b_1551_, 0);
v_snd_1585_ = lean_ctor_get(v_b_1551_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_b_1551_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1587_ = v_b_1551_;
v_isShared_1588_ = v_isSharedCheck_1633_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_inc(v_fst_1584_);
lean_dec(v_b_1551_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1633_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_toConstantVal_1589_; lean_object* v_numParams_1590_; lean_object* v___f_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v_a_1595_; 
v_toConstantVal_1589_ = lean_ctor_get(v_indVal_1547_, 0);
v_numParams_1590_ = lean_ctor_get(v_indVal_1547_, 1);
v___f_1591_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0));
v___x_1592_ = lean_array_fget_borrowed(v_xs_1546_, v_a_1550_);
v___x_1593_ = lean_nat_dec_lt(v_a_1550_, v_numParams_1590_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1));
v___x_1620_ = l_Lean_Core_mkFreshUserName(v___x_1619_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_a_1595_ = v_a_1621_;
goto v___jp_1594_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_del_object(v___x_1587_);
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_dec(v_a_1550_);
lean_dec(v_auxFunName_1548_);
v_a_1622_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1620_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_argNames_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_argNames_1630_ = lean_ctor_get(v_header_1549_, 1);
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_array_get_borrowed(v___x_1631_, v_argNames_1630_, v_a_1550_);
lean_inc(v___x_1632_);
v_a_1595_ = v___x_1632_;
goto v___jp_1594_;
}
v___jp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_mkIdent(v_a_1595_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_del_object(v___x_1587_);
lean_inc(v___x_1596_);
v___x_1597_ = lean_array_push(v_fst_1584_, v___x_1596_);
v___x_1598_ = lean_box(0);
lean_inc(v_auxFunName_1548_);
lean_inc(v___x_1592_);
v___x_1599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1591_, v_snd_1585_, v___x_1596_, v___x_1592_, v_toConstantVal_1589_, v_auxFunName_1548_, v___x_1598_, v___x_1597_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
v___y_1560_ = v___x_1599_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_n(v_a_1601_, 2);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1603_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 2);
lean_ctor_set(v___x_1587_, 1, v___x_1603_);
lean_ctor_set(v___x_1587_, 0, v_a_1601_);
v___x_1605_ = v___x_1587_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = l_Lean_Syntax_node1(v_a_1601_, v___x_1602_, v___x_1605_);
v___x_1607_ = lean_array_push(v_fst_1584_, v___x_1606_);
v___x_1608_ = lean_box(0);
lean_inc(v_auxFunName_1548_);
lean_inc(v___x_1592_);
v___x_1609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___f_1591_, v_snd_1585_, v___x_1596_, v___x_1592_, v_toConstantVal_1589_, v_auxFunName_1548_, v___x_1608_, v___x_1607_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
v___y_1560_ = v___x_1609_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v___x_1596_);
lean_del_object(v___x_1587_);
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_dec(v_a_1550_);
lean_dec(v_auxFunName_1548_);
v_a_1611_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1600_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1600_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
}
}
v___jp_1559_:
{
if (lean_obj_tag(v___y_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1573_; 
v_a_1561_ = lean_ctor_get(v___y_1560_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___y_1560_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1563_ = v___y_1560_;
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___y_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
if (lean_obj_tag(v_a_1561_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; 
lean_dec(v_a_1550_);
lean_dec(v_auxFunName_1548_);
v_a_1565_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v_a_1561_, 1);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v_a_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_del_object(v___x_1563_);
v_a_1569_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v_a_1561_, 1);
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_add(v_a_1550_, v___x_1570_);
lean_dec(v_a_1550_);
v_a_1550_ = v___x_1571_;
v_b_1551_ = v_a_1569_;
goto _start;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_a_1550_);
lean_dec(v_auxFunName_1548_);
v_a_1574_ = lean_ctor_get(v___y_1560_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___y_1560_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___y_1560_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___y_1560_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1545_ = stack[0].m_obj;
lean_object* v_xs_1546_ = stack[1].m_obj;
lean_object* v_indVal_1547_ = stack[2].m_obj;
lean_object* v_auxFunName_1548_ = stack[3].m_obj;
lean_object* v_header_1549_ = stack[4].m_obj;
lean_object* v_a_1550_ = stack[5].m_obj;
lean_object* v_b_1551_ = stack[6].m_obj;
lean_object* v___y_1552_ = stack[7].m_obj;
lean_object* v___y_1553_ = stack[8].m_obj;
lean_object* v___y_1554_ = stack[9].m_obj;
lean_object* v___y_1555_ = stack[10].m_obj;
lean_object* v___y_1556_ = stack[11].m_obj;
lean_object* v___y_1557_ = stack[12].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_1545_, v_xs_1546_, v_indVal_1547_, v_auxFunName_1548_, v_header_1549_, v_a_1550_, v_b_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1635_, lean_object* v_xs_1636_, lean_object* v_indVal_1637_, lean_object* v_auxFunName_1638_, lean_object* v_header_1639_, lean_object* v_a_1640_, lean_object* v_b_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_1635_, v_xs_1636_, v_indVal_1637_, v_auxFunName_1638_, v_header_1639_, v_a_1640_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_header_1639_);
lean_dec_ref(v_indVal_1637_);
lean_dec_ref(v_xs_1636_);
lean_dec(v_upperBound_1635_);
return v_res_1649_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4));
v___x_1663_ = l_String_toRawSubstring_x27(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15));
v___x_1688_ = l_Lean_mkAtom(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18));
v___x_1692_ = l_String_toRawSubstring_x27(v___x_1691_);
return v___x_1692_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object* v_indVal_1748_, lean_object* v___x_1749_, lean_object* v_alts_1750_, lean_object* v_name_1751_, lean_object* v_auxFunName_1752_, lean_object* v_header_1753_, lean_object* v___f_1754_, lean_object* v_head_1755_, lean_object* v_xs_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_numIndices_1765_; lean_object* v___x_1766_; 
v_numIndices_1765_ = lean_ctor_get(v_indVal_1748_, 2);
lean_inc_ref(v_alts_1750_);
lean_inc(v___x_1749_);
v___x_1766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_numIndices_1765_, v___x_1749_, v_alts_1750_, v___y_1762_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_toCold_1767_; lean_object* v_a_1768_; lean_object* v_ref_1769_; lean_object* v_quotContext_1770_; lean_object* v_currMacroScope_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_toCold_1767_ = lean_ctor_get(v___y_1762_, 0);
v_a_1768_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1766_, 1);
v_ref_1769_ = lean_ctor_get(v___y_1762_, 2);
v_quotContext_1770_ = lean_ctor_get(v_toCold_1767_, 8);
v_currMacroScope_1771_ = lean_ctor_get(v_toCold_1767_, 9);
v___x_1772_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1));
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_array_get_size(v_xs_1756_);
v___x_1775_ = 0;
v___x_1776_ = l_Lean_SourceInfo_fromRef(v_ref_1769_, v___x_1775_);
v___x_1777_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5);
lean_inc(v_currMacroScope_1771_);
lean_inc(v_quotContext_1770_);
v___x_1778_ = l_Lean_addMacroScope(v_quotContext_1770_, v___x_1772_, v_currMacroScope_1771_);
v___x_1779_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8));
lean_inc_n(v___x_1776_, 2);
v___x_1780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1776_);
lean_ctor_set(v___x_1780_, 1, v___x_1777_);
lean_ctor_set(v___x_1780_, 2, v___x_1778_);
lean_ctor_set(v___x_1780_, 3, v___x_1779_);
v___x_1781_ = 1;
v___x_1782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1751_, v___x_1781_);
v___x_1783_ = lean_box(2);
v___x_1784_ = l_Lean_Syntax_mkStrLit(v___x_1782_, v___x_1783_);
v___x_1785_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1786_ = l_Lean_Syntax_node1(v___x_1776_, v___x_1785_, v___x_1784_);
v___x_1787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31));
v___x_1788_ = l_Lean_Syntax_node2(v___x_1776_, v___x_1787_, v___x_1780_, v___x_1786_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_alts_1750_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v___x_1774_, v_xs_1756_, v_indVal_1748_, v_auxFunName_1752_, v_header_1753_, v___x_1749_, v___x_1789_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1916_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v_fst_1792_ = lean_ctor_get(v_a_1791_, 0);
v_snd_1793_ = lean_ctor_get(v_a_1791_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_a_1791_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1795_ = v_a_1791_;
v_isShared_1796_ = v_isSharedCheck_1916_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_snd_1793_);
lean_inc(v_fst_1792_);
lean_dec(v_a_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1916_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; 
lean_inc_ref(v___f_1754_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
v___x_1797_ = lean_apply_7(v___f_1754_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, lean_box(0));
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc_n(v_a_1798_, 2);
lean_dec_ref_known(v___x_1797_, 1);
v___x_1799_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10));
v___x_1800_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11));
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 2);
lean_ctor_set(v___x_1795_, 1, v___x_1800_);
lean_ctor_set(v___x_1795_, 0, v_a_1798_);
v___x_1802_ = v___x_1795_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1798_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1803_ = l_Lean_mkIdent(v_head_1755_);
lean_inc_n(v_a_1798_, 2);
v___x_1804_ = l_Lean_Syntax_node2(v_a_1798_, v___x_1799_, v___x_1802_, v___x_1803_);
v___x_1805_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_1806_ = l_Array_append___redArg(v___x_1805_, v_fst_1792_);
lean_dec(v_fst_1792_);
v___x_1807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1798_);
lean_ctor_set(v___x_1807_, 1, v___x_1785_);
lean_ctor_set(v___x_1807_, 2, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node2(v_a_1798_, v___x_1787_, v___x_1804_, v___x_1807_);
v___x_1809_ = lean_array_push(v_a_1768_, v___x_1808_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
v___x_1810_ = lean_apply_7(v___f_1754_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, lean_box(0));
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1898_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1898_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1898_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; size_t v_sz_1818_; size_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1815_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13));
v___x_1816_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14));
lean_inc_n(v_a_1811_, 35);
v___x_1817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_a_1811_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v_sz_1818_ = lean_array_size(v___x_1809_);
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_1818_, v___x_1819_, v___x_1809_);
v___x_1821_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_1822_ = l_Lean_mkSepArray(v___x_1820_, v___x_1821_);
lean_dec_ref(v___x_1820_);
v___x_1823_ = l_Array_append___redArg(v___x_1805_, v___x_1822_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1811_);
lean_ctor_set(v___x_1824_, 1, v___x_1785_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = l_Lean_Syntax_node1(v_a_1811_, v___x_1785_, v___x_1824_);
v___x_1826_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17));
v___x_1827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_a_1811_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19);
v___x_1829_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21));
lean_inc_n(v_currMacroScope_1771_, 5);
lean_inc_n(v_quotContext_1770_, 5);
v___x_1830_ = l_Lean_addMacroScope(v_quotContext_1770_, v___x_1829_, v_currMacroScope_1771_);
v___x_1831_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23));
v___x_1832_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1832_, 0, v_a_1811_);
lean_ctor_set(v___x_1832_, 1, v___x_1828_);
lean_ctor_set(v___x_1832_, 2, v___x_1830_);
lean_ctor_set(v___x_1832_, 3, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7));
v___x_1834_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9));
v___x_1835_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_1836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1811_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11));
v___x_1838_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13);
v___x_1839_ = lean_box(0);
v___x_1840_ = l_Lean_addMacroScope(v_quotContext_1770_, v___x_1839_, v_currMacroScope_1771_);
v___x_1841_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27));
v___x_1842_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1842_, 0, v_a_1811_);
lean_ctor_set(v___x_1842_, 1, v___x_1838_);
lean_ctor_set(v___x_1842_, 2, v___x_1840_);
lean_ctor_set(v___x_1842_, 3, v___x_1841_);
v___x_1843_ = l_Lean_Syntax_node1(v_a_1811_, v___x_1837_, v___x_1842_);
v___x_1844_ = l_Lean_Syntax_node2(v_a_1811_, v___x_1834_, v___x_1836_, v___x_1843_);
v___x_1845_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33);
v___x_1846_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36));
v___x_1847_ = l_Lean_addMacroScope(v_quotContext_1770_, v___x_1846_, v_currMacroScope_1771_);
v___x_1848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30));
v___x_1849_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1811_);
lean_ctor_set(v___x_1849_, 1, v___x_1845_);
lean_ctor_set(v___x_1849_, 2, v___x_1847_);
lean_ctor_set(v___x_1849_, 3, v___x_1848_);
v___x_1850_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43);
v___x_1851_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45));
v___x_1852_ = l_Lean_addMacroScope(v_quotContext_1770_, v___x_1851_, v_currMacroScope_1771_);
v___x_1853_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33));
v___x_1854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1811_);
lean_ctor_set(v___x_1854_, 1, v___x_1850_);
lean_ctor_set(v___x_1854_, 2, v___x_1852_);
lean_ctor_set(v___x_1854_, 3, v___x_1853_);
v___x_1855_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35));
v___x_1856_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36));
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_a_1811_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38));
v___x_1859_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
v___x_1861_ = l_Lean_addMacroScope(v_quotContext_1770_, v___x_1860_, v_currMacroScope_1771_);
v___x_1862_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1862_, 0, v_a_1811_);
lean_ctor_set(v___x_1862_, 1, v___x_1859_);
lean_ctor_set(v___x_1862_, 2, v___x_1861_);
lean_ctor_set(v___x_1862_, 3, v___x_1773_);
v___x_1863_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39));
v___x_1864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_a_1811_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1866_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_a_1811_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_Syntax_node1(v_a_1811_, v___x_1865_, v___x_1867_);
lean_inc_ref(v___x_1862_);
v___x_1869_ = l_Lean_Syntax_node3(v_a_1811_, v___x_1858_, v___x_1862_, v___x_1864_, v___x_1868_);
v___x_1870_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40));
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1811_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42));
v___x_1873_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43));
v___x_1874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_a_1811_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node1(v_a_1811_, v___x_1872_, v___x_1874_);
v___x_1876_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44));
v___x_1877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_a_1811_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45));
v___x_1879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1811_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_Syntax_node1(v_a_1811_, v___x_1872_, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_node6(v_a_1811_, v___x_1855_, v___x_1857_, v___x_1869_, v___x_1871_, v___x_1875_, v___x_1877_, v___x_1880_);
v___x_1882_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_1883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_a_1811_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
lean_inc_ref_n(v___x_1883_, 3);
lean_inc_n(v___x_1844_, 3);
v___x_1884_ = l_Lean_Syntax_node3(v_a_1811_, v___x_1833_, v___x_1844_, v___x_1881_, v___x_1883_);
v___x_1885_ = l_Lean_Syntax_node3(v_a_1811_, v___x_1833_, v___x_1844_, v_snd_1793_, v___x_1883_);
v___x_1886_ = l_Lean_Syntax_node2(v_a_1811_, v___x_1785_, v___x_1884_, v___x_1885_);
v___x_1887_ = l_Lean_Syntax_node2(v_a_1811_, v___x_1787_, v___x_1854_, v___x_1886_);
v___x_1888_ = l_Lean_Syntax_node3(v_a_1811_, v___x_1833_, v___x_1844_, v___x_1887_, v___x_1883_);
v___x_1889_ = l_Lean_Syntax_node1(v_a_1811_, v___x_1785_, v___x_1888_);
v___x_1890_ = l_Lean_Syntax_node2(v_a_1811_, v___x_1787_, v___x_1849_, v___x_1889_);
v___x_1891_ = l_Lean_Syntax_node3(v_a_1811_, v___x_1833_, v___x_1844_, v___x_1890_, v___x_1883_);
v___x_1892_ = l_Lean_Syntax_node2(v_a_1811_, v___x_1785_, v___x_1891_, v___x_1862_);
v___x_1893_ = l_Lean_Syntax_node2(v_a_1811_, v___x_1787_, v___x_1832_, v___x_1892_);
v___x_1894_ = l_Lean_Syntax_node4(v_a_1811_, v___x_1815_, v___x_1817_, v___x_1825_, v___x_1827_, v___x_1893_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1894_);
v___x_1896_ = v___x_1813_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v___x_1809_);
lean_dec(v_snd_1793_);
v_a_1899_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1810_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1810_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_del_object(v___x_1795_);
lean_dec(v_snd_1793_);
lean_dec(v_fst_1792_);
lean_dec(v_a_1768_);
lean_dec(v_head_1755_);
lean_dec_ref(v___f_1754_);
v_a_1908_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1797_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1797_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1768_);
lean_dec(v_head_1755_);
lean_dec_ref(v___f_1754_);
v_a_1917_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1790_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1790_);
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
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_head_1755_);
lean_dec_ref(v___f_1754_);
lean_dec(v_auxFunName_1752_);
lean_dec(v_name_1751_);
lean_dec_ref(v_alts_1750_);
lean_dec(v___x_1749_);
v_a_1925_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1766_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1766_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_1748_ = stack[0].m_obj;
lean_object* v___x_1749_ = stack[1].m_obj;
lean_object* v_alts_1750_ = stack[2].m_obj;
lean_object* v_name_1751_ = stack[3].m_obj;
lean_object* v_auxFunName_1752_ = stack[4].m_obj;
lean_object* v_header_1753_ = stack[5].m_obj;
lean_object* v___f_1754_ = stack[6].m_obj;
lean_object* v_head_1755_ = stack[7].m_obj;
lean_object* v_xs_1756_ = stack[8].m_obj;
lean_object* v_x_1757_ = stack[9].m_obj;
lean_object* v___y_1758_ = stack[10].m_obj;
lean_object* v___y_1759_ = stack[11].m_obj;
lean_object* v___y_1760_ = stack[12].m_obj;
lean_object* v___y_1761_ = stack[13].m_obj;
lean_object* v___y_1762_ = stack[14].m_obj;
lean_object* v___y_1763_ = stack[15].m_obj;
lean_object* v_res_1933_;
v_res_1933_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(v_indVal_1748_, v___x_1749_, v_alts_1750_, v_name_1751_, v_auxFunName_1752_, v_header_1753_, v___f_1754_, v_head_1755_, v_xs_1756_, v_x_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
stack->m_obj
 = v_res_1933_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1934_ = _args[0];
lean_object* v___x_1935_ = _args[1];
lean_object* v_alts_1936_ = _args[2];
lean_object* v_name_1937_ = _args[3];
lean_object* v_auxFunName_1938_ = _args[4];
lean_object* v_header_1939_ = _args[5];
lean_object* v___f_1940_ = _args[6];
lean_object* v_head_1941_ = _args[7];
lean_object* v_xs_1942_ = _args[8];
lean_object* v_x_1943_ = _args[9];
lean_object* v___y_1944_ = _args[10];
lean_object* v___y_1945_ = _args[11];
lean_object* v___y_1946_ = _args[12];
lean_object* v___y_1947_ = _args[13];
lean_object* v___y_1948_ = _args[14];
lean_object* v___y_1949_ = _args[15];
lean_object* v___y_1950_ = _args[16];
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(v_indVal_1934_, v___x_1935_, v_alts_1936_, v_name_1937_, v_auxFunName_1938_, v_header_1939_, v___f_1940_, v_head_1941_, v_xs_1942_, v_x_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_x_1943_);
lean_dec_ref(v_xs_1942_);
lean_dec_ref(v_header_1939_);
lean_dec_ref(v_indVal_1934_);
return v_res_1951_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_ref_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_ref_1959_ = lean_ctor_get(v___y_1956_, 2);
v___x_1960_ = 0;
v___x_1961_ = l_Lean_SourceInfo_fromRef(v_ref_1959_, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1952_ = stack[0].m_obj;
lean_object* v___y_1953_ = stack[1].m_obj;
lean_object* v___y_1954_ = stack[2].m_obj;
lean_object* v___y_1955_ = stack[3].m_obj;
lean_object* v___y_1956_ = stack[4].m_obj;
lean_object* v___y_1957_ = stack[5].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1971_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object* v_indVal_1975_, lean_object* v_auxFunName_1976_, lean_object* v_header_1977_, lean_object* v_as_x27_1978_, lean_object* v_b_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
if (lean_obj_tag(v_as_x27_1978_) == 0)
{
lean_object* v___x_1987_; 
lean_dec_ref(v_header_1977_);
lean_dec(v_auxFunName_1976_);
lean_dec_ref(v_indVal_1975_);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_b_1979_);
return v___x_1987_;
}
else
{
lean_object* v_head_1988_; lean_object* v_tail_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v_alts_1992_; lean_object* v___x_1993_; 
v_head_1988_ = lean_ctor_get(v_as_x27_1978_, 0);
v_tail_1989_ = lean_ctor_get(v_as_x27_1978_, 1);
v___f_1990_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0));
v___x_1991_ = lean_unsigned_to_nat(0u);
v_alts_1992_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
lean_inc(v_head_1988_);
v___x_1993_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_head_1988_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v_toConstantVal_1995_; lean_object* v_name_1996_; lean_object* v_type_1997_; lean_object* v___f_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v_toConstantVal_1995_ = lean_ctor_get(v_a_1994_, 0);
lean_inc_ref(v_toConstantVal_1995_);
lean_dec(v_a_1994_);
v_name_1996_ = lean_ctor_get(v_toConstantVal_1995_, 0);
lean_inc(v_name_1996_);
v_type_1997_ = lean_ctor_get(v_toConstantVal_1995_, 2);
lean_inc_ref(v_type_1997_);
lean_dec_ref(v_toConstantVal_1995_);
lean_inc(v_head_1988_);
lean_inc_ref(v_header_1977_);
lean_inc(v_auxFunName_1976_);
lean_inc_ref(v_indVal_1975_);
v___f_1998_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1998_, 0, v_indVal_1975_);
lean_closure_set(v___f_1998_, 1, v___x_1991_);
lean_closure_set(v___f_1998_, 2, v_alts_1992_);
lean_closure_set(v___f_1998_, 3, v_name_1996_);
lean_closure_set(v___f_1998_, 4, v_auxFunName_1976_);
lean_closure_set(v___f_1998_, 5, v_header_1977_);
lean_closure_set(v___f_1998_, 6, v___f_1990_);
lean_closure_set(v___f_1998_, 7, v_head_1988_);
v___x_1999_ = 0;
v___x_2000_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_1997_, v___f_1998_, v___x_1999_, v___x_1999_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = lean_array_push(v_b_1979_, v_a_2001_);
v_as_x27_1978_ = v_tail_1989_;
v_b_1979_ = v___x_2002_;
goto _start;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_b_1979_);
lean_dec_ref(v_header_1977_);
lean_dec(v_auxFunName_1976_);
lean_dec_ref(v_indVal_1975_);
v_a_2004_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2000_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2000_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_b_1979_);
lean_dec_ref(v_header_1977_);
lean_dec(v_auxFunName_1976_);
lean_dec_ref(v_indVal_1975_);
v_a_2012_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1993_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1993_);
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
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_1975_ = stack[0].m_obj;
lean_object* v_auxFunName_1976_ = stack[1].m_obj;
lean_object* v_header_1977_ = stack[2].m_obj;
lean_object* v_as_x27_1978_ = stack[3].m_obj;
lean_object* v_b_1979_ = stack[4].m_obj;
lean_object* v___y_1980_ = stack[5].m_obj;
lean_object* v___y_1981_ = stack[6].m_obj;
lean_object* v___y_1982_ = stack[7].m_obj;
lean_object* v___y_1983_ = stack[8].m_obj;
lean_object* v___y_1984_ = stack[9].m_obj;
lean_object* v___y_1985_ = stack[10].m_obj;
lean_object* v_res_2020_;
v_res_2020_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_1975_, v_auxFunName_1976_, v_header_1977_, v_as_x27_1978_, v_b_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
stack->m_obj
 = v_res_2020_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object* v_indVal_2021_, lean_object* v_auxFunName_2022_, lean_object* v_header_2023_, lean_object* v_as_x27_2024_, lean_object* v_b_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2021_, v_auxFunName_2022_, v_header_2023_, v_as_x27_2024_, v_b_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v_as_x27_2024_);
return v_res_2033_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t v_sz_2034_, size_t v_i_2035_, lean_object* v_bs_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
if (v___x_2037_ == 0)
{
return v_bs_2036_;
}
else
{
lean_object* v_v_2038_; lean_object* v___x_2039_; lean_object* v_bs_x27_2040_; size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v_v_2038_ = lean_array_uget(v_bs_2036_, v_i_2035_);
v___x_2039_ = lean_unsigned_to_nat(0u);
v_bs_x27_2040_ = lean_array_uset(v_bs_2036_, v_i_2035_, v___x_2039_);
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_add(v_i_2035_, v___x_2041_);
v___x_2043_ = lean_array_uset(v_bs_x27_2040_, v_i_2035_, v_v_2038_);
v_i_2035_ = v___x_2042_;
v_bs_2036_ = v___x_2043_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2034_ = stack[0].m_num;
size_t v_i_2035_ = stack[1].m_num;
lean_object* v_bs_2036_ = stack[2].m_obj;
lean_object* v_res_2045_;
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_2034_, v_i_2035_, v_bs_2036_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_sz_2046_, lean_object* v_i_2047_, lean_object* v_bs_2048_){
_start:
{
size_t v_sz_boxed_2049_; size_t v_i_boxed_2050_; lean_object* v_res_2051_; 
v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2046_);
lean_dec(v_sz_2046_);
v_i_boxed_2050_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_boxed_2049_, v_i_boxed_2050_, v_bs_2048_);
return v_res_2051_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object* v_header_2052_, lean_object* v_indVal_2053_, lean_object* v_auxFunName_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_ctors_2062_; lean_object* v_alts_2063_; lean_object* v___x_2064_; 
v_ctors_2062_ = lean_ctor_get(v_indVal_2053_, 4);
lean_inc(v_ctors_2062_);
v_alts_2063_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2064_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2053_, v_auxFunName_2054_, v_header_2052_, v_ctors_2062_, v_alts_2063_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_ctors_2062_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2075_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2075_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2075_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
size_t v_sz_2069_; size_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v_sz_2069_ = lean_array_size(v_a_2065_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_2069_, v___x_2070_, v_a_2065_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2071_);
v___x_2073_ = v___x_2067_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
return v___x_2064_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_2052_ = stack[0].m_obj;
lean_object* v_indVal_2053_ = stack[1].m_obj;
lean_object* v_auxFunName_2054_ = stack[2].m_obj;
lean_object* v_a_2055_ = stack[3].m_obj;
lean_object* v_a_2056_ = stack[4].m_obj;
lean_object* v_a_2057_ = stack[5].m_obj;
lean_object* v_a_2058_ = stack[6].m_obj;
lean_object* v_a_2059_ = stack[7].m_obj;
lean_object* v_a_2060_ = stack[8].m_obj;
lean_object* v_res_2076_;
v_res_2076_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2052_, v_indVal_2053_, v_auxFunName_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
stack->m_obj
 = v_res_2076_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object* v_header_2077_, lean_object* v_indVal_2078_, lean_object* v_auxFunName_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2077_, v_indVal_2078_, v_auxFunName_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
return v_res_2087_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object* v_upperBound_2088_, lean_object* v_xs_2089_, lean_object* v_indVal_2090_, lean_object* v_auxFunName_2091_, lean_object* v_header_2092_, lean_object* v_inst_2093_, lean_object* v_R_2094_, lean_object* v_a_2095_, lean_object* v_b_2096_, lean_object* v_c_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_2088_, v_xs_2089_, v_indVal_2090_, v_auxFunName_2091_, v_header_2092_, v_a_2095_, v_b_2096_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2088_ = stack[0].m_obj;
lean_object* v_xs_2089_ = stack[1].m_obj;
lean_object* v_indVal_2090_ = stack[2].m_obj;
lean_object* v_auxFunName_2091_ = stack[3].m_obj;
lean_object* v_header_2092_ = stack[4].m_obj;
lean_object* v_a_2095_ = stack[7].m_obj;
lean_object* v_b_2096_ = stack[8].m_obj;
lean_object* v___y_2098_ = stack[10].m_obj;
lean_object* v___y_2099_ = stack[11].m_obj;
lean_object* v___y_2100_ = stack[12].m_obj;
lean_object* v___y_2101_ = stack[13].m_obj;
lean_object* v___y_2102_ = stack[14].m_obj;
lean_object* v___y_2103_ = stack[15].m_obj;
lean_object* v_res_2106_;
v_res_2106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(v_upperBound_2088_, v_xs_2089_, v_indVal_2090_, v_auxFunName_2091_, v_header_2092_, lean_box(0), lean_box(0), v_a_2095_, v_b_2096_, lean_box(0), v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
stack->m_obj
 = v_res_2106_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2107_ = _args[0];
lean_object* v_xs_2108_ = _args[1];
lean_object* v_indVal_2109_ = _args[2];
lean_object* v_auxFunName_2110_ = _args[3];
lean_object* v_header_2111_ = _args[4];
lean_object* v_inst_2112_ = _args[5];
lean_object* v_R_2113_ = _args[6];
lean_object* v_a_2114_ = _args[7];
lean_object* v_b_2115_ = _args[8];
lean_object* v_c_2116_ = _args[9];
lean_object* v___y_2117_ = _args[10];
lean_object* v___y_2118_ = _args[11];
lean_object* v___y_2119_ = _args[12];
lean_object* v___y_2120_ = _args[13];
lean_object* v___y_2121_ = _args[14];
lean_object* v___y_2122_ = _args[15];
lean_object* v___y_2123_ = _args[16];
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(v_upperBound_2107_, v_xs_2108_, v_indVal_2109_, v_auxFunName_2110_, v_header_2111_, v_inst_2112_, v_R_2113_, v_a_2114_, v_b_2115_, v_c_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_header_2111_);
lean_dec_ref(v_indVal_2109_);
lean_dec_ref(v_xs_2108_);
lean_dec(v_upperBound_2107_);
return v_res_2124_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object* v_upperBound_2125_, lean_object* v_inst_2126_, lean_object* v_R_2127_, lean_object* v_a_2128_, lean_object* v_b_2129_, lean_object* v_c_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_2125_, v_a_2128_, v_b_2129_, v___y_2135_);
return v___x_2138_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2125_ = stack[0].m_obj;
lean_object* v_a_2128_ = stack[3].m_obj;
lean_object* v_b_2129_ = stack[4].m_obj;
lean_object* v___y_2131_ = stack[6].m_obj;
lean_object* v___y_2132_ = stack[7].m_obj;
lean_object* v___y_2133_ = stack[8].m_obj;
lean_object* v___y_2134_ = stack[9].m_obj;
lean_object* v___y_2135_ = stack[10].m_obj;
lean_object* v___y_2136_ = stack[11].m_obj;
lean_object* v_res_2139_;
v_res_2139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(v_upperBound_2125_, lean_box(0), lean_box(0), v_a_2128_, v_b_2129_, lean_box(0), v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
stack->m_obj
 = v_res_2139_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object* v_upperBound_2140_, lean_object* v_inst_2141_, lean_object* v_R_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_, lean_object* v_c_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(v_upperBound_2140_, v_inst_2141_, v_R_2142_, v_a_2143_, v_b_2144_, v_c_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v_upperBound_2140_);
return v_res_2153_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object* v_indVal_2154_, lean_object* v_auxFunName_2155_, lean_object* v_header_2156_, lean_object* v_as_2157_, lean_object* v_as_x27_2158_, lean_object* v_b_2159_, lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2154_, v_auxFunName_2155_, v_header_2156_, v_as_x27_2158_, v_b_2159_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_2154_ = stack[0].m_obj;
lean_object* v_auxFunName_2155_ = stack[1].m_obj;
lean_object* v_header_2156_ = stack[2].m_obj;
lean_object* v_as_2157_ = stack[3].m_obj;
lean_object* v_as_x27_2158_ = stack[4].m_obj;
lean_object* v_b_2159_ = stack[5].m_obj;
lean_object* v___y_2161_ = stack[7].m_obj;
lean_object* v___y_2162_ = stack[8].m_obj;
lean_object* v___y_2163_ = stack[9].m_obj;
lean_object* v___y_2164_ = stack[10].m_obj;
lean_object* v___y_2165_ = stack[11].m_obj;
lean_object* v___y_2166_ = stack[12].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(v_indVal_2154_, v_auxFunName_2155_, v_header_2156_, v_as_2157_, v_as_x27_2158_, v_b_2159_, lean_box(0), v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_indVal_2170_, lean_object* v_auxFunName_2171_, lean_object* v_header_2172_, lean_object* v_as_2173_, lean_object* v_as_x27_2174_, lean_object* v_b_2175_, lean_object* v_a_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(v_indVal_2170_, v_auxFunName_2171_, v_header_2172_, v_as_2173_, v_as_x27_2174_, v_b_2175_, v_a_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v_as_x27_2174_);
lean_dec(v_as_2173_);
return v_res_2184_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object* v_header_2198_, lean_object* v_indVal_2199_, lean_object* v_auxFunName_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___x_2208_; 
lean_inc_ref(v_indVal_2199_);
lean_inc_ref(v_header_2198_);
v___x_2208_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2198_, v_indVal_2199_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2198_, v_indVal_2199_, v_auxFunName_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2241_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2241_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2241_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_ref_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; size_t v_sz_2224_; size_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v_ref_2215_ = lean_ctor_get(v_a_2205_, 2);
v___x_2216_ = 0;
v___x_2217_ = l_Lean_SourceInfo_fromRef(v_ref_2215_, v___x_2216_);
v___x_2218_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0));
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1));
lean_inc_n(v___x_2217_, 6);
v___x_2220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2217_);
lean_ctor_set(v___x_2220_, 1, v___x_2218_);
v___x_2221_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2222_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2217_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2222_);
v_sz_2224_ = lean_array_size(v_a_2209_);
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_2224_, v___x_2225_, v_a_2209_);
v___x_2227_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_2228_ = l_Lean_mkSepArray(v___x_2226_, v___x_2227_);
lean_dec_ref(v___x_2226_);
v___x_2229_ = l_Array_append___redArg(v___x_2222_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2217_);
lean_ctor_set(v___x_2230_, 1, v___x_2221_);
lean_ctor_set(v___x_2230_, 2, v___x_2229_);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2));
v___x_2232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2217_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4));
v___x_2234_ = l_Array_append___redArg(v___x_2222_, v_a_2211_);
lean_dec(v_a_2211_);
v___x_2235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2217_);
lean_ctor_set(v___x_2235_, 1, v___x_2221_);
lean_ctor_set(v___x_2235_, 2, v___x_2234_);
v___x_2236_ = l_Lean_Syntax_node1(v___x_2217_, v___x_2233_, v___x_2235_);
lean_inc_ref(v___x_2223_);
v___x_2237_ = l_Lean_Syntax_node6(v___x_2217_, v___x_2219_, v___x_2220_, v___x_2223_, v___x_2223_, v___x_2230_, v___x_2232_, v___x_2236_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2237_);
v___x_2239_ = v___x_2213_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
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
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_a_2209_);
v_a_2242_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2210_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2210_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_auxFunName_2200_);
lean_dec_ref(v_indVal_2199_);
lean_dec_ref(v_header_2198_);
v_a_2250_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2208_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2208_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkBodyForInduct_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_2198_ = stack[0].m_obj;
lean_object* v_indVal_2199_ = stack[1].m_obj;
lean_object* v_auxFunName_2200_ = stack[2].m_obj;
lean_object* v_a_2201_ = stack[3].m_obj;
lean_object* v_a_2202_ = stack[4].m_obj;
lean_object* v_a_2203_ = stack[5].m_obj;
lean_object* v_a_2204_ = stack[6].m_obj;
lean_object* v_a_2205_ = stack[7].m_obj;
lean_object* v_a_2206_ = stack[8].m_obj;
lean_object* v_res_2258_;
v_res_2258_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2198_, v_indVal_2199_, v_auxFunName_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
stack->m_obj
 = v_res_2258_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object* v_header_2259_, lean_object* v_indVal_2260_, lean_object* v_auxFunName_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2259_, v_indVal_2260_, v_auxFunName_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2269_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object* v_header_2270_, lean_object* v_indVal_2271_, lean_object* v_auxFunName_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2280_; lean_object* v_toConstantVal_2281_; lean_object* v_env_2282_; lean_object* v_name_2283_; uint8_t v___x_2284_; 
v___x_2280_ = lean_st_ref_get(v_a_2278_);
v_toConstantVal_2281_ = lean_ctor_get(v_indVal_2271_, 0);
v_env_2282_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_env_2282_);
lean_dec(v___x_2280_);
v_name_2283_ = lean_ctor_get(v_toConstantVal_2281_, 0);
lean_inc(v_name_2283_);
v___x_2284_ = l_Lean_isStructure(v_env_2282_, v_name_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2270_, v_indVal_2271_, v_auxFunName_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; 
lean_dec(v_auxFunName_2272_);
v___x_2286_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_2270_, v_indVal_2271_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec_ref(v_header_2270_);
return v___x_2286_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkBody_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_2270_ = stack[0].m_obj;
lean_object* v_indVal_2271_ = stack[1].m_obj;
lean_object* v_auxFunName_2272_ = stack[2].m_obj;
lean_object* v_a_2273_ = stack[3].m_obj;
lean_object* v_a_2274_ = stack[4].m_obj;
lean_object* v_a_2275_ = stack[5].m_obj;
lean_object* v_a_2276_ = stack[6].m_obj;
lean_object* v_a_2277_ = stack[7].m_obj;
lean_object* v_a_2278_ = stack[8].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l_Lean_Elab_Deriving_Repr_mkBody(v_header_2270_, v_indVal_2271_, v_auxFunName_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object* v_header_2288_, lean_object* v_indVal_2289_, lean_object* v_auxFunName_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Elab_Deriving_Repr_mkBody(v_header_2288_, v_indVal_2289_, v_auxFunName_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15));
v___x_2340_ = l_String_toRawSubstring_x27(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34));
v___x_2370_ = l_String_toRawSubstring_x27(v___x_2369_);
return v___x_2370_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object* v_ctx_2407_, lean_object* v_i_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_typeInfos_2416_; lean_object* v_auxFunNames_2417_; uint8_t v_usePartial_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v_auxFunName_2421_; lean_object* v_indVal_2422_; lean_object* v___x_2423_; 
v_typeInfos_2416_ = lean_ctor_get(v_ctx_2407_, 1);
v_auxFunNames_2417_ = lean_ctor_get(v_ctx_2407_, 2);
v_usePartial_2418_ = lean_ctor_get_uint8(v_ctx_2407_, sizeof(void*)*3);
v___x_2419_ = lean_box(0);
v___x_2420_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_2421_ = lean_array_get_borrowed(v___x_2419_, v_auxFunNames_2417_, v_i_2408_);
v_indVal_2422_ = lean_array_get_borrowed(v___x_2420_, v_typeInfos_2416_, v_i_2408_);
lean_inc(v_indVal_2422_);
v___x_2423_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_2422_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2596_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2596_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2596_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_body_2429_; lean_object* v___y_2430_; lean_object* v___x_2579_; 
lean_inc(v_auxFunName_2421_);
lean_inc(v_indVal_2422_);
lean_inc(v_a_2424_);
v___x_2579_ = l_Lean_Elab_Deriving_Repr_mkBody(v_a_2424_, v_indVal_2422_, v_auxFunName_2421_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
if (lean_obj_tag(v___x_2579_) == 0)
{
if (v_usePartial_2418_ == 0)
{
lean_object* v_a_2580_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v_body_2429_ = v_a_2580_;
v___y_2430_ = v_a_2413_;
goto v___jp_2428_;
}
else
{
lean_object* v_a_2581_; lean_object* v_argNames_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_a_2581_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2579_, 1);
v_argNames_2582_ = lean_ctor_get(v_a_2424_, 1);
v___x_2583_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
lean_inc_ref(v_argNames_2582_);
v___x_2584_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2407_, v___x_2583_, v_argNames_2582_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = l_Lean_Elab_Deriving_mkLet(v_a_2585_, v_a_2581_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2585_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v_body_2429_ = v_a_2587_;
v___y_2430_ = v_a_2413_;
goto v___jp_2428_;
}
else
{
lean_del_object(v___x_2426_);
lean_dec(v_a_2424_);
return v___x_2586_;
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_a_2581_);
lean_del_object(v___x_2426_);
lean_dec(v_a_2424_);
v_a_2588_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2584_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2584_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
else
{
lean_del_object(v___x_2426_);
lean_dec(v_a_2424_);
return v___x_2579_;
}
v___jp_2428_:
{
if (v_usePartial_2418_ == 0)
{
lean_object* v_toCold_2431_; lean_object* v_binders_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2498_; 
v_toCold_2431_ = lean_ctor_get(v___y_2430_, 0);
v_binders_2432_ = lean_ctor_get(v_a_2424_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_a_2424_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; 
v_unused_2499_ = lean_ctor_get(v_a_2424_, 3);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_a_2424_, 2);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_a_2424_, 1);
lean_dec(v_unused_2501_);
v___x_2434_ = v_a_2424_;
v_isShared_2435_ = v_isSharedCheck_2498_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_binders_2432_);
lean_dec(v_a_2424_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2498_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v_ref_2436_; lean_object* v_quotContext_2437_; lean_object* v_currMacroScope_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v_ref_2436_ = lean_ctor_get(v___y_2430_, 2);
v_quotContext_2437_ = lean_ctor_get(v_toCold_2431_, 8);
v_currMacroScope_2438_ = lean_ctor_get(v_toCold_2431_, 9);
v___x_2439_ = l_Lean_SourceInfo_fromRef(v_ref_2436_, v_usePartial_2418_);
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2442_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2443_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2439_, 4);
v___x_2444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2439_);
lean_ctor_set(v___x_2444_, 1, v___x_2442_);
lean_ctor_set(v___x_2444_, 2, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2439_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2444_);
v___x_2450_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2449_, v___x_2444_);
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2452_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2438_);
lean_inc(v_quotContext_2437_);
v___x_2454_ = l_Lean_addMacroScope(v_quotContext_2437_, v___x_2453_, v_currMacroScope_2438_);
v___x_2455_ = lean_box(0);
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 3);
lean_ctor_set(v___x_2434_, 3, v___x_2455_);
lean_ctor_set(v___x_2434_, 2, v___x_2454_);
lean_ctor_set(v___x_2434_, 1, v___x_2452_);
lean_ctor_set(v___x_2434_, 0, v___x_2439_);
v___x_2457_ = v___x_2434_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
lean_inc_ref_n(v___x_2444_, 11);
lean_inc_n(v___x_2439_, 19);
v___x_2458_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2451_, v___x_2457_, v___x_2444_);
v___x_2459_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2448_, v___x_2450_, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2442_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2439_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_Syntax_node3(v___x_2439_, v___x_2445_, v___x_2447_, v___x_2460_, v___x_2462_);
v___x_2464_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2442_, v___x_2463_);
v___x_2465_ = l_Lean_Syntax_node7(v___x_2439_, v___x_2441_, v___x_2444_, v___x_2464_, v___x_2444_, v___x_2444_, v___x_2444_, v___x_2444_, v___x_2444_);
v___x_2466_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2467_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2439_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2421_);
v___x_2470_ = l_Lean_mkIdent(v_auxFunName_2421_);
v___x_2471_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2469_, v___x_2470_, v___x_2444_);
v___x_2472_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2473_ = l_Array_append___redArg(v___x_2443_, v_binders_2432_);
lean_dec_ref(v_binders_2432_);
v___x_2474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2439_);
lean_ctor_set(v___x_2474_, 1, v___x_2442_);
lean_ctor_set(v___x_2474_, 2, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2439_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2479_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2438_);
lean_inc(v_quotContext_2437_);
v___x_2480_ = l_Lean_addMacroScope(v_quotContext_2437_, v___x_2479_, v_currMacroScope_2438_);
v___x_2481_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2439_);
lean_ctor_set(v___x_2482_, 1, v___x_2478_);
lean_ctor_set(v___x_2482_, 2, v___x_2480_);
lean_ctor_set(v___x_2482_, 3, v___x_2481_);
v___x_2483_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2475_, v___x_2477_, v___x_2482_);
v___x_2484_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2442_, v___x_2483_);
v___x_2485_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2472_, v___x_2474_, v___x_2484_);
v___x_2486_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2487_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2439_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2490_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2489_, v___x_2444_, v___x_2444_);
v___x_2491_ = l_Lean_Syntax_node4(v___x_2439_, v___x_2486_, v___x_2488_, v_body_2429_, v___x_2490_, v___x_2444_);
v___x_2492_ = l_Lean_Syntax_node5(v___x_2439_, v___x_2466_, v___x_2468_, v___x_2471_, v___x_2485_, v___x_2491_, v___x_2444_);
v___x_2493_ = l_Lean_Syntax_node2(v___x_2439_, v___x_2440_, v___x_2465_, v___x_2492_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2493_);
v___x_2495_ = v___x_2426_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_object* v_toCold_2502_; lean_object* v_binders_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2575_; 
v_toCold_2502_ = lean_ctor_get(v___y_2430_, 0);
v_binders_2503_ = lean_ctor_get(v_a_2424_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_a_2424_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; lean_object* v_unused_2577_; lean_object* v_unused_2578_; 
v_unused_2576_ = lean_ctor_get(v_a_2424_, 3);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v_a_2424_, 2);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v_a_2424_, 1);
lean_dec(v_unused_2578_);
v___x_2505_ = v_a_2424_;
v_isShared_2506_ = v_isSharedCheck_2575_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_binders_2503_);
lean_dec(v_a_2424_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2575_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v_ref_2507_; lean_object* v_quotContext_2508_; lean_object* v_currMacroScope_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v_ref_2507_ = lean_ctor_get(v___y_2430_, 2);
v_quotContext_2508_ = lean_ctor_get(v_toCold_2502_, 8);
v_currMacroScope_2509_ = lean_ctor_get(v_toCold_2502_, 9);
v___x_2510_ = 0;
v___x_2511_ = l_Lean_SourceInfo_fromRef(v_ref_2507_, v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2513_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2514_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2515_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2511_, 4);
v___x_2516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2511_);
lean_ctor_set(v___x_2516_, 1, v___x_2514_);
lean_ctor_set(v___x_2516_, 2, v___x_2515_);
v___x_2517_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2511_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2521_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2516_);
v___x_2522_ = l_Lean_Syntax_node1(v___x_2511_, v___x_2521_, v___x_2516_);
v___x_2523_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2524_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2525_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2509_);
lean_inc(v_quotContext_2508_);
v___x_2526_ = l_Lean_addMacroScope(v_quotContext_2508_, v___x_2525_, v_currMacroScope_2509_);
v___x_2527_ = lean_box(0);
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 3);
lean_ctor_set(v___x_2505_, 3, v___x_2527_);
lean_ctor_set(v___x_2505_, 2, v___x_2526_);
lean_ctor_set(v___x_2505_, 1, v___x_2524_);
lean_ctor_set(v___x_2505_, 0, v___x_2511_);
v___x_2529_ = v___x_2505_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_inc_ref_n(v___x_2516_, 10);
lean_inc_n(v___x_2511_, 22);
v___x_2530_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2523_, v___x_2529_, v___x_2516_);
v___x_2531_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2520_, v___x_2522_, v___x_2530_);
v___x_2532_ = l_Lean_Syntax_node1(v___x_2511_, v___x_2514_, v___x_2531_);
v___x_2533_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2511_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = l_Lean_Syntax_node3(v___x_2511_, v___x_2517_, v___x_2519_, v___x_2532_, v___x_2534_);
v___x_2536_ = l_Lean_Syntax_node1(v___x_2511_, v___x_2514_, v___x_2535_);
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41));
v___x_2538_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42));
v___x_2539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2511_);
lean_ctor_set(v___x_2539_, 1, v___x_2537_);
v___x_2540_ = l_Lean_Syntax_node1(v___x_2511_, v___x_2538_, v___x_2539_);
v___x_2541_ = l_Lean_Syntax_node1(v___x_2511_, v___x_2514_, v___x_2540_);
v___x_2542_ = l_Lean_Syntax_node7(v___x_2511_, v___x_2513_, v___x_2516_, v___x_2536_, v___x_2516_, v___x_2516_, v___x_2516_, v___x_2516_, v___x_2541_);
v___x_2543_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2511_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2421_);
v___x_2547_ = l_Lean_mkIdent(v_auxFunName_2421_);
v___x_2548_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2546_, v___x_2547_, v___x_2516_);
v___x_2549_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2550_ = l_Array_append___redArg(v___x_2515_, v_binders_2503_);
lean_dec_ref(v_binders_2503_);
v___x_2551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2511_);
lean_ctor_set(v___x_2551_, 1, v___x_2514_);
lean_ctor_set(v___x_2551_, 2, v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2553_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2511_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2509_);
lean_inc(v_quotContext_2508_);
v___x_2557_ = l_Lean_addMacroScope(v_quotContext_2508_, v___x_2556_, v_currMacroScope_2509_);
v___x_2558_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2511_);
lean_ctor_set(v___x_2559_, 1, v___x_2555_);
lean_ctor_set(v___x_2559_, 2, v___x_2557_);
lean_ctor_set(v___x_2559_, 3, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2552_, v___x_2554_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node1(v___x_2511_, v___x_2514_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2549_, v___x_2551_, v___x_2561_);
v___x_2563_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2564_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2511_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2567_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2566_, v___x_2516_, v___x_2516_);
v___x_2568_ = l_Lean_Syntax_node4(v___x_2511_, v___x_2563_, v___x_2565_, v_body_2429_, v___x_2567_, v___x_2516_);
v___x_2569_ = l_Lean_Syntax_node5(v___x_2511_, v___x_2543_, v___x_2545_, v___x_2548_, v___x_2562_, v___x_2568_, v___x_2516_);
v___x_2570_ = l_Lean_Syntax_node2(v___x_2511_, v___x_2512_, v___x_2542_, v___x_2569_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2570_);
v___x_2572_ = v___x_2426_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
v_a_2597_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2423_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2423_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkAuxFunction_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2407_ = stack[0].m_obj;
lean_object* v_i_2408_ = stack[1].m_obj;
lean_object* v_a_2409_ = stack[2].m_obj;
lean_object* v_a_2410_ = stack[3].m_obj;
lean_object* v_a_2411_ = stack[4].m_obj;
lean_object* v_a_2412_ = stack[5].m_obj;
lean_object* v_a_2413_ = stack[6].m_obj;
lean_object* v_a_2414_ = stack[7].m_obj;
lean_object* v_res_2605_;
v_res_2605_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2407_, v_i_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
stack->m_obj
 = v_res_2605_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object* v_ctx_2606_, lean_object* v_i_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2606_, v_i_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_i_2607_);
lean_dec_ref(v_ctx_2606_);
return v_res_2615_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2616_, lean_object* v_ctx_2617_, lean_object* v_a_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_nat_dec_lt(v_a_2618_, v_upperBound_2616_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_dec(v_a_2618_);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_b_2619_);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2617_, v_a_2618_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = lean_array_push(v_b_2619_, v_a_2630_);
v___x_2632_ = lean_unsigned_to_nat(1u);
v___x_2633_ = lean_nat_add(v_a_2618_, v___x_2632_);
lean_dec(v_a_2618_);
v_a_2618_ = v___x_2633_;
v_b_2619_ = v___x_2631_;
goto _start;
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v_b_2619_);
lean_dec(v_a_2618_);
v_a_2635_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2629_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2629_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2616_ = stack[0].m_obj;
lean_object* v_ctx_2617_ = stack[1].m_obj;
lean_object* v_a_2618_ = stack[2].m_obj;
lean_object* v_b_2619_ = stack[3].m_obj;
lean_object* v___y_2620_ = stack[4].m_obj;
lean_object* v___y_2621_ = stack[5].m_obj;
lean_object* v___y_2622_ = stack[6].m_obj;
lean_object* v___y_2623_ = stack[7].m_obj;
lean_object* v___y_2624_ = stack[8].m_obj;
lean_object* v___y_2625_ = stack[9].m_obj;
lean_object* v_res_2643_;
v_res_2643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2616_, v_ctx_2617_, v_a_2618_, v_b_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2644_, lean_object* v_ctx_2645_, lean_object* v_a_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2644_, v_ctx_2645_, v_a_2646_, v_b_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v_ctx_2645_);
lean_dec(v_upperBound_2644_);
return v_res_2655_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object* v_ctx_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_typeInfos_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v_auxDefs_2674_; lean_object* v___x_2675_; 
v_typeInfos_2671_ = lean_ctor_get(v_ctx_2663_, 1);
v___x_2672_ = lean_array_get_size(v_typeInfos_2671_);
v___x_2673_ = lean_unsigned_to_nat(0u);
v_auxDefs_2674_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v___x_2672_, v_ctx_2663_, v___x_2673_, v_auxDefs_2674_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2696_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2696_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2696_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_ref_2680_; uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v_ref_2680_ = lean_ctor_get(v_a_2668_, 2);
v___x_2681_ = 0;
v___x_2682_ = l_Lean_SourceInfo_fromRef(v_ref_2680_, v___x_2681_);
v___x_2683_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0));
v___x_2684_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1));
lean_inc_n(v___x_2682_, 3);
v___x_2685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2682_);
lean_ctor_set(v___x_2685_, 1, v___x_2683_);
v___x_2686_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2687_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2688_ = l_Array_append___redArg(v___x_2687_, v_a_2676_);
lean_dec(v_a_2676_);
v___x_2689_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2682_);
lean_ctor_set(v___x_2689_, 1, v___x_2686_);
lean_ctor_set(v___x_2689_, 2, v___x_2688_);
v___x_2690_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2));
v___x_2691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2682_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = l_Lean_Syntax_node3(v___x_2682_, v___x_2684_, v___x_2685_, v___x_2689_, v___x_2691_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2692_);
v___x_2694_ = v___x_2678_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
v_a_2697_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2675_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2675_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkMutualBlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2663_ = stack[0].m_obj;
lean_object* v_a_2664_ = stack[1].m_obj;
lean_object* v_a_2665_ = stack[2].m_obj;
lean_object* v_a_2666_ = stack[3].m_obj;
lean_object* v_a_2667_ = stack[4].m_obj;
lean_object* v_a_2668_ = stack[5].m_obj;
lean_object* v_a_2669_ = stack[6].m_obj;
lean_object* v_res_2705_;
v_res_2705_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_ctx_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
stack->m_obj
 = v_res_2705_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object* v_ctx_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_ctx_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec_ref(v_ctx_2706_);
return v_res_2714_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object* v_upperBound_2715_, lean_object* v_ctx_2716_, lean_object* v_inst_2717_, lean_object* v_R_2718_, lean_object* v_a_2719_, lean_object* v_b_2720_, lean_object* v_c_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2715_, v_ctx_2716_, v_a_2719_, v_b_2720_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2715_ = stack[0].m_obj;
lean_object* v_ctx_2716_ = stack[1].m_obj;
lean_object* v_a_2719_ = stack[4].m_obj;
lean_object* v_b_2720_ = stack[5].m_obj;
lean_object* v___y_2722_ = stack[7].m_obj;
lean_object* v___y_2723_ = stack[8].m_obj;
lean_object* v___y_2724_ = stack[9].m_obj;
lean_object* v___y_2725_ = stack[10].m_obj;
lean_object* v___y_2726_ = stack[11].m_obj;
lean_object* v___y_2727_ = stack[12].m_obj;
lean_object* v_res_2730_;
v_res_2730_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(v_upperBound_2715_, v_ctx_2716_, lean_box(0), lean_box(0), v_a_2719_, v_b_2720_, lean_box(0), v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
stack->m_obj
 = v_res_2730_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2731_, lean_object* v_ctx_2732_, lean_object* v_inst_2733_, lean_object* v_R_2734_, lean_object* v_a_2735_, lean_object* v_b_2736_, lean_object* v_c_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(v_upperBound_2731_, v_ctx_2732_, v_inst_2733_, v_R_2734_, v_a_2735_, v_b_2736_, v_c_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v_ctx_2732_);
lean_dec(v_upperBound_2731_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
if (lean_obj_tag(v_a_2746_) == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = l_List_reverse___redArg(v_a_2747_);
return v___x_2748_;
}
else
{
lean_object* v_head_2749_; lean_object* v_tail_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2759_; 
v_head_2749_ = lean_ctor_get(v_a_2746_, 0);
v_tail_2750_ = lean_ctor_get(v_a_2746_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_a_2746_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2752_ = v_a_2746_;
v_isShared_2753_ = v_isSharedCheck_2759_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_tail_2750_);
lean_inc(v_head_2749_);
lean_dec(v_a_2746_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2759_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2754_ = l_Lean_MessageData_ofSyntax(v_head_2749_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v_a_2747_);
lean_ctor_set(v___x_2752_, 0, v___x_2754_);
v___x_2756_ = v___x_2752_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_a_2747_);
v___x_2756_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
v_a_2746_ = v_tail_2750_;
v_a_2747_ = v___x_2756_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2760_; double v___x_2761_; 
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_float_of_nat(v___x_2760_);
return v___x_2761_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object* v_cls_2764_, lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_ref_2771_; lean_object* v___x_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2818_; 
v_ref_2771_ = lean_ctor_get(v___y_2768_, 2);
v___x_2772_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2818_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2818_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v_traceState_2778_; lean_object* v_env_2779_; lean_object* v_nextMacroScope_2780_; lean_object* v_ngen_2781_; lean_object* v_auxDeclNGen_2782_; lean_object* v_cache_2783_; lean_object* v_recordedDeps_2784_; lean_object* v_messages_2785_; lean_object* v_infoState_2786_; lean_object* v_snapshotTasks_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2817_; 
v___x_2777_ = lean_st_ref_take(v___y_2769_);
v_traceState_2778_ = lean_ctor_get(v___x_2777_, 4);
v_env_2779_ = lean_ctor_get(v___x_2777_, 0);
v_nextMacroScope_2780_ = lean_ctor_get(v___x_2777_, 1);
v_ngen_2781_ = lean_ctor_get(v___x_2777_, 2);
v_auxDeclNGen_2782_ = lean_ctor_get(v___x_2777_, 3);
v_cache_2783_ = lean_ctor_get(v___x_2777_, 5);
v_recordedDeps_2784_ = lean_ctor_get(v___x_2777_, 6);
v_messages_2785_ = lean_ctor_get(v___x_2777_, 7);
v_infoState_2786_ = lean_ctor_get(v___x_2777_, 8);
v_snapshotTasks_2787_ = lean_ctor_get(v___x_2777_, 9);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2789_ = v___x_2777_;
v_isShared_2790_ = v_isSharedCheck_2817_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_snapshotTasks_2787_);
lean_inc(v_infoState_2786_);
lean_inc(v_messages_2785_);
lean_inc(v_recordedDeps_2784_);
lean_inc(v_cache_2783_);
lean_inc(v_traceState_2778_);
lean_inc(v_auxDeclNGen_2782_);
lean_inc(v_ngen_2781_);
lean_inc(v_nextMacroScope_2780_);
lean_inc(v_env_2779_);
lean_dec(v___x_2777_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2817_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
uint64_t v_tid_2791_; lean_object* v_traces_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2816_; 
v_tid_2791_ = lean_ctor_get_uint64(v_traceState_2778_, sizeof(void*)*1);
v_traces_2792_ = lean_ctor_get(v_traceState_2778_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_traceState_2778_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2794_ = v_traceState_2778_;
v_isShared_2795_ = v_isSharedCheck_2816_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_traces_2792_);
lean_dec(v_traceState_2778_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2816_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; double v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0);
v___x_2799_ = 0;
v___x_2800_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12));
v___x_2801_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2801_, 0, v_cls_2764_);
lean_ctor_set(v___x_2801_, 1, v___x_2797_);
lean_ctor_set(v___x_2801_, 2, v___x_2800_);
lean_ctor_set_float(v___x_2801_, sizeof(void*)*3, v___x_2798_);
lean_ctor_set_float(v___x_2801_, sizeof(void*)*3 + 8, v___x_2798_);
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*3 + 16, v___x_2799_);
v___x_2802_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1));
v___x_2803_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v_a_2773_);
lean_ctor_set(v___x_2803_, 2, v___x_2802_);
lean_inc(v_ref_2771_);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v_ref_2771_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_PersistentArray_push___redArg(v_traces_2792_, v___x_2804_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2805_);
v___x_2807_ = v___x_2794_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2805_);
lean_ctor_set_uint64(v_reuseFailAlloc_2815_, sizeof(void*)*1, v_tid_2791_);
v___x_2807_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 4, v___x_2807_);
v___x_2809_ = v___x_2789_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_env_2779_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_nextMacroScope_2780_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_ngen_2781_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_auxDeclNGen_2782_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2814_, 5, v_cache_2783_);
lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_recordedDeps_2784_);
lean_ctor_set(v_reuseFailAlloc_2814_, 7, v_messages_2785_);
lean_ctor_set(v_reuseFailAlloc_2814_, 8, v_infoState_2786_);
lean_ctor_set(v_reuseFailAlloc_2814_, 9, v_snapshotTasks_2787_);
v___x_2809_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_put(v___y_2769_, v___x_2809_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2796_);
v___x_2812_ = v___x_2775_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2796_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2764_ = stack[0].m_obj;
lean_object* v_msg_2765_ = stack[1].m_obj;
lean_object* v___y_2766_ = stack[2].m_obj;
lean_object* v___y_2767_ = stack[3].m_obj;
lean_object* v___y_2768_ = stack[4].m_obj;
lean_object* v___y_2769_ = stack[5].m_obj;
lean_object* v_res_2819_;
v_res_2819_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2764_, v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
stack->m_obj
 = v_res_2819_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object* v_cls_2820_, lean_object* v_msg_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2820_, v_msg_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
return v_res_2827_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2836_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2));
v___x_2837_ = l_Lean_Name_append(v___x_2836_, v___x_2835_);
return v___x_2837_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4));
v___x_2840_ = l_Lean_stringToMessageData(v___x_2839_);
return v___x_2840_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object* v_declName_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_2850_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51));
v___x_2851_ = 1;
lean_inc(v_declName_2841_);
v___x_2852_ = l_Lean_Elab_Deriving_mkContext(v___x_2849_, v___x_2850_, v_declName_2841_, v___x_2851_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_a_2853_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = lean_mk_empty_array_with_capacity(v___x_2856_);
lean_inc_ref(v___x_2857_);
v___x_2858_ = lean_array_push(v___x_2857_, v_declName_2841_);
v___x_2859_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_2853_, v___x_2849_, v___x_2858_, v___x_2851_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
lean_dec_ref(v___x_2858_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_toCold_2860_; lean_object* v_options_2861_; lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2902_; 
v_toCold_2860_ = lean_ctor_get(v_a_2846_, 0);
v_options_2861_ = lean_ctor_get(v_toCold_2860_, 2);
v_a_2862_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2864_ = v___x_2859_;
v_isShared_2865_ = v_isSharedCheck_2902_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2859_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2902_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_inheritedTraceOptions_2866_; uint8_t v_hasTrace_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_inheritedTraceOptions_2866_ = lean_ctor_get(v_toCold_2860_, 11);
v_hasTrace_2867_ = lean_ctor_get_uint8(v_options_2861_, sizeof(void*)*1);
v___x_2868_ = lean_array_push(v___x_2857_, v_a_2855_);
v___x_2869_ = l_Array_append___redArg(v___x_2868_, v_a_2862_);
lean_dec(v_a_2862_);
if (v_hasTrace_2867_ == 0)
{
lean_object* v___x_2871_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2869_);
v___x_2871_ = v___x_2864_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2874_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3);
v___x_2875_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2866_, v_options_2861_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2877_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2869_);
v___x_2877_ = v___x_2864_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2869_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_del_object(v___x_2864_);
v___x_2879_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5);
lean_inc_ref(v___x_2869_);
v___x_2880_ = lean_array_to_list(v___x_2869_);
v___x_2881_ = lean_box(0);
v___x_2882_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(v___x_2880_, v___x_2881_);
v___x_2883_ = l_Lean_MessageData_ofList(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2879_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v___x_2873_, v___x_2884_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2893_);
v___x_2887_ = v___x_2885_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v___x_2885_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2869_);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2869_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v___x_2869_);
v_a_2894_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2885_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2885_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v___x_2857_);
lean_dec(v_a_2855_);
v_a_2903_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2859_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2859_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2853_);
lean_dec(v_declName_2841_);
v_a_2911_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2854_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2854_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_declName_2841_);
v_a_2919_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2852_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2852_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2841_ = stack[0].m_obj;
lean_object* v_a_2842_ = stack[1].m_obj;
lean_object* v_a_2843_ = stack[2].m_obj;
lean_object* v_a_2844_ = stack[3].m_obj;
lean_object* v_a_2845_ = stack[4].m_obj;
lean_object* v_a_2846_ = stack[5].m_obj;
lean_object* v_a_2847_ = stack[6].m_obj;
lean_object* v_res_2927_;
v_res_2927_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(v_declName_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
stack->m_obj
 = v_res_2927_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object* v_declName_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(v_declName_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
return v_res_2936_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object* v_cls_2937_, lean_object* v_msg_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2937_, v_msg_2938_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2937_ = stack[0].m_obj;
lean_object* v_msg_2938_ = stack[1].m_obj;
lean_object* v___y_2939_ = stack[2].m_obj;
lean_object* v___y_2940_ = stack[3].m_obj;
lean_object* v___y_2941_ = stack[4].m_obj;
lean_object* v___y_2942_ = stack[5].m_obj;
lean_object* v___y_2943_ = stack[6].m_obj;
lean_object* v___y_2944_ = stack[7].m_obj;
lean_object* v_res_2947_;
v_res_2947_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(v_cls_2937_, v_msg_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
stack->m_obj
 = v_res_2947_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object* v_cls_2948_, lean_object* v_msg_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(v_cls_2948_, v_msg_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2957_;
}
}
lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object* v_declName_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; lean_object* v_env_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2961_ = lean_st_ref_get(v___y_2959_);
v_env_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_ref(v_env_2962_);
lean_dec(v___x_2961_);
v___x_2963_ = l_Lean_isInductiveCore(v_env_2962_, v_declName_2958_);
v___x_2964_ = lean_box(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2958_ = stack[0].m_obj;
lean_object* v___y_2959_ = stack[1].m_obj;
lean_object* v_res_2966_;
v_res_2966_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2958_, v___y_2959_);
stack->m_obj
 = v_res_2966_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2967_, v___y_2968_);
lean_dec(v___y_2968_);
return v_res_2970_;
}
}
lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object* v_declName_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2971_, v___y_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2971_ = stack[0].m_obj;
lean_object* v___y_2972_ = stack[1].m_obj;
lean_object* v___y_2973_ = stack[2].m_obj;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(v_declName_2971_, v___y_2972_, v___y_2973_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object* v_declName_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(v_declName_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
return v_res_2981_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t v_____do__lift_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
if (v_____do__lift_2982_ == 0)
{
uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = 1;
v___x_2987_ = lean_box(v___x_2986_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
else
{
uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = 0;
v___x_2990_ = lean_box(v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_2982_ = stack[0].m_num;
lean_object* v___y_2983_ = stack[1].m_obj;
lean_object* v___y_2984_ = stack[2].m_obj;
lean_object* v_res_2992_;
v_res_2992_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v_____do__lift_2982_, v___y_2983_, v___y_2984_);
stack->m_obj
 = v_res_2992_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
uint8_t v_____do__lift_2296__boxed_2997_; lean_object* v_res_2998_; 
v_____do__lift_2296__boxed_2997_ = lean_unbox(v_____do__lift_2993_);
v_res_2998_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v_____do__lift_2296__boxed_2997_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
return v_res_2998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object* v_as_2999_, size_t v_i_3000_, size_t v_stop_3001_, lean_object* v_b_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_eq(v_i_3000_, v_stop_3001_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_array_uget_borrowed(v_as_2999_, v_i_3000_);
lean_inc(v___x_3007_);
v___x_3008_ = l_Lean_Elab_Command_elabCommand(v___x_3007_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; size_t v___x_3010_; size_t v___x_3011_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3000_, v___x_3010_);
v_i_3000_ = v___x_3011_;
v_b_3002_ = v_a_3009_;
goto _start;
}
else
{
return v___x_3008_;
}
}
else
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_b_3002_);
return v___x_3013_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2999_ = stack[0].m_obj;
size_t v_i_3000_ = stack[1].m_num;
size_t v_stop_3001_ = stack[2].m_num;
lean_object* v_b_3002_ = stack[3].m_obj;
lean_object* v___y_3003_ = stack[4].m_obj;
lean_object* v___y_3004_ = stack[5].m_obj;
lean_object* v_res_3014_;
v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_as_2999_, v_i_3000_, v_stop_3001_, v_b_3002_, v___y_3003_, v___y_3004_);
stack->m_obj
 = v_res_3014_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object* v_as_3015_, lean_object* v_i_3016_, lean_object* v_stop_3017_, lean_object* v_b_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
size_t v_i_boxed_3022_; size_t v_stop_boxed_3023_; lean_object* v_res_3024_; 
v_i_boxed_3022_ = lean_unbox_usize(v_i_3016_);
lean_dec(v_i_3016_);
v_stop_boxed_3023_ = lean_unbox_usize(v_stop_3017_);
lean_dec(v_stop_3017_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_as_3015_, v_i_boxed_3022_, v_stop_boxed_3023_, v_b_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v_as_3015_);
return v_res_3024_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object* v___x_3025_, lean_object* v___x_3026_, lean_object* v___x_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_3025_, v___y_3028_, v___y_3029_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3051_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3051_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3051_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = lean_array_get_size(v_a_3032_);
v___x_3037_ = lean_nat_dec_lt(v___x_3026_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3039_; 
lean_dec(v_a_3032_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3027_);
v___x_3039_ = v___x_3034_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3027_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_nat_dec_le(v___x_3036_, v___x_3036_);
if (v___x_3041_ == 0)
{
if (v___x_3037_ == 0)
{
lean_object* v___x_3043_; 
lean_dec(v_a_3032_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3027_);
v___x_3043_ = v___x_3034_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3027_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
lean_del_object(v___x_3034_);
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = lean_usize_of_nat(v___x_3036_);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_3032_, v___x_3045_, v___x_3046_, v___x_3027_, v___y_3028_, v___y_3029_);
lean_dec(v_a_3032_);
return v___x_3047_;
}
}
else
{
size_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
lean_del_object(v___x_3034_);
v___x_3048_ = ((size_t)0ULL);
v___x_3049_ = lean_usize_of_nat(v___x_3036_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_3032_, v___x_3048_, v___x_3049_, v___x_3027_, v___y_3028_, v___y_3029_);
lean_dec(v_a_3032_);
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3031_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3031_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3025_ = stack[0].m_obj;
lean_object* v___x_3026_ = stack[1].m_obj;
lean_object* v___x_3027_ = stack[2].m_obj;
lean_object* v___y_3028_ = stack[3].m_obj;
lean_object* v___y_3029_ = stack[4].m_obj;
lean_object* v_res_3060_;
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(v___x_3025_, v___x_3026_, v___x_3027_, v___y_3028_, v___y_3029_);
stack->m_obj
 = v_res_3060_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object* v___x_3061_, lean_object* v___x_3062_, lean_object* v___x_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(v___x_3061_, v___x_3062_, v___x_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___x_3062_);
return v_res_3067_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object* v_as_3068_, size_t v_sz_3069_, size_t v_i_3070_, lean_object* v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_usize_dec_lt(v_i_3070_, v_sz_3069_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3071_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_a_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; 
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = lean_box(0);
v_a_3079_ = lean_array_uget_borrowed(v_as_3068_, v_i_3070_);
lean_inc_n(v_a_3079_, 2);
v___x_3080_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed), 8, 1);
lean_closure_set(v___x_3080_, 0, v_a_3079_);
v___f_3081_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3081_, 0, v___x_3080_);
lean_closure_set(v___f_3081_, 1, v___x_3077_);
lean_closure_set(v___f_3081_, 2, v___x_3078_);
v___x_3082_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_3079_, v___f_3081_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3082_) == 0)
{
size_t v___x_3083_; size_t v___x_3084_; 
lean_dec_ref_known(v___x_3082_, 1);
v___x_3083_ = ((size_t)1ULL);
v___x_3084_ = lean_usize_add(v_i_3070_, v___x_3083_);
v_i_3070_ = v___x_3084_;
v_b_3071_ = v___x_3078_;
goto _start;
}
else
{
return v___x_3082_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3068_ = stack[0].m_obj;
size_t v_sz_3069_ = stack[1].m_num;
size_t v_i_3070_ = stack[2].m_num;
lean_object* v_b_3071_ = stack[3].m_obj;
lean_object* v___y_3072_ = stack[4].m_obj;
lean_object* v___y_3073_ = stack[5].m_obj;
lean_object* v_res_3086_;
v_res_3086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_as_3068_, v_sz_3069_, v_i_3070_, v_b_3071_, v___y_3072_, v___y_3073_);
stack->m_obj
 = v_res_3086_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object* v_as_3087_, lean_object* v_sz_3088_, lean_object* v_i_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
size_t v_sz_boxed_3094_; size_t v_i_boxed_3095_; lean_object* v_res_3096_; 
v_sz_boxed_3094_ = lean_unbox_usize(v_sz_3088_);
lean_dec(v_sz_3088_);
v_i_boxed_3095_ = lean_unbox_usize(v_i_3089_);
lean_dec(v_i_3089_);
v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_as_3087_, v_sz_boxed_3094_, v_i_boxed_3095_, v_b_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec_ref(v_as_3087_);
return v_res_3096_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object* v_as_3097_, size_t v_i_3098_, size_t v_stop_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_usize_dec_eq(v_i_3098_, v_stop_3099_);
if (v___x_3107_ == 0)
{
uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = 1;
v___x_3109_ = lean_array_uget_borrowed(v_as_3097_, v_i_3098_);
lean_inc(v___x_3109_);
v___x_3110_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v___x_3109_, v___y_3101_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3120_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_unbox(v_a_3111_);
lean_dec(v_a_3111_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_box(v___x_3108_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3116_);
v___x_3118_ = v___x_3113_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
else
{
lean_del_object(v___x_3113_);
goto v___jp_3103_;
}
}
}
else
{
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3130_; 
v_a_3121_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3123_ = v___x_3110_;
v_isShared_3124_ = v_isSharedCheck_3130_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3110_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3130_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_unbox(v_a_3121_);
lean_dec(v_a_3121_);
if (v___x_3125_ == 0)
{
lean_del_object(v___x_3123_);
goto v___jp_3103_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_box(v___x_3108_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3126_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
return v___x_3110_;
}
}
}
else
{
uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = 0;
v___x_3132_ = lean_box(v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
v___jp_3103_:
{
size_t v___x_3104_; size_t v___x_3105_; 
v___x_3104_ = ((size_t)1ULL);
v___x_3105_ = lean_usize_add(v_i_3098_, v___x_3104_);
v_i_3098_ = v___x_3105_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3097_ = stack[0].m_obj;
size_t v_i_3098_ = stack[1].m_num;
size_t v_stop_3099_ = stack[2].m_num;
lean_object* v___y_3100_ = stack[3].m_obj;
lean_object* v___y_3101_ = stack[4].m_obj;
lean_object* v_res_3134_;
v_res_3134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_as_3097_, v_i_3098_, v_stop_3099_, v___y_3100_, v___y_3101_);
stack->m_obj
 = v_res_3134_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object* v_as_3135_, lean_object* v_i_3136_, lean_object* v_stop_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
size_t v_i_boxed_3141_; size_t v_stop_boxed_3142_; lean_object* v_res_3143_; 
v_i_boxed_3141_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_stop_boxed_3142_ = lean_unbox_usize(v_stop_3137_);
lean_dec(v_stop_3137_);
v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_as_3135_, v_i_boxed_3141_, v_stop_boxed_3142_, v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec_ref(v_as_3135_);
return v_res_3143_;
}
}
lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object* v_declNames_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v___y_3172_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = lean_array_get_size(v_declNames_3144_);
v___x_3177_ = lean_nat_dec_lt(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3177_, v_a_3145_, v_a_3146_);
v___y_3172_ = v___x_3178_;
goto v___jp_3171_;
}
else
{
if (v___x_3177_ == 0)
{
goto v___jp_3148_;
}
else
{
size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = lean_usize_of_nat(v___x_3176_);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_declNames_3144_, v___x_3179_, v___x_3180_, v_a_3145_, v_a_3146_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; uint8_t v___x_3183_; lean_object* v___x_3184_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = lean_unbox(v_a_3182_);
lean_dec(v_a_3182_);
v___x_3184_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3183_, v_a_3145_, v_a_3146_);
v___y_3172_ = v___x_3184_;
goto v___jp_3171_;
}
else
{
v___y_3172_ = v___x_3181_;
goto v___jp_3171_;
}
}
}
v___jp_3148_:
{
uint8_t v___x_3149_; lean_object* v___x_3150_; size_t v_sz_3151_; size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = 1;
v___x_3150_ = lean_box(0);
v_sz_3151_ = lean_array_size(v_declNames_3144_);
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_declNames_3144_, v_sz_3151_, v___x_3152_, v___x_3150_, v_a_3145_, v_a_3146_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3161_; 
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___x_3153_, 0);
lean_dec(v_unused_3162_);
v___x_3155_ = v___x_3153_;
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
else
{
lean_dec(v___x_3153_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = lean_box(v___x_3149_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3157_);
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_a_3163_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3153_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3153_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
v___jp_3171_:
{
if (lean_obj_tag(v___y_3172_) == 0)
{
lean_object* v_a_3173_; uint8_t v___x_3174_; 
v_a_3173_ = lean_ctor_get(v___y_3172_, 0);
v___x_3174_ = lean_unbox(v_a_3173_);
if (v___x_3174_ == 0)
{
return v___y_3172_;
}
else
{
lean_dec_ref_known(v___y_3172_, 1);
goto v___jp_3148_;
}
}
else
{
return v___y_3172_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_3144_ = stack[0].m_obj;
lean_object* v_a_3145_ = stack[1].m_obj;
lean_object* v_a_3146_ = stack[2].m_obj;
lean_object* v_res_3185_;
v_res_3185_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(v_declNames_3144_, v_a_3145_, v_a_3146_);
stack->m_obj
 = v_res_3185_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object* v_declNames_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(v_declNames_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec_ref(v_declNames_3186_);
return v_res_3190_;
}
}
lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3258_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_3259_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3260_ = l_Lean_Elab_registerDerivingHandler(v___x_3258_, v___x_3259_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec_ref_known(v___x_3260_, 1);
v___x_3261_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_3262_ = 0;
v___x_3263_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3264_ = l_Lean_registerTraceClass(v___x_3261_, v___x_3262_, v___x_3263_);
return v___x_3264_;
}
else
{
return v___x_3260_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3265_;
v_res_3265_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
return v_res_3267_;
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
